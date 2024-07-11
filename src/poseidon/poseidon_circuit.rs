use std::{convert::TryInto, num::NonZeroUsize};

use ff::{FromUniformBytes, PrimeField, PrimeFieldBits};
use halo2_proofs::{
    circuit::{AssignedCell, Chip, Value},
    halo2curves::ff,
    plonk::Error,
};
use poseidon::{self};
use tracing::*;

use super::{ROCircuitTrait, Spec};
use crate::{
    constants::MAX_BITS,
    main_gate::{AssignedBit, AssignedValue, MainGate, MainGateConfig, RegionCtx, WrapValue},
};

pub struct PoseidonChip<F: PrimeFieldBits, const T: usize, const RATE: usize> {
    main_gate: MainGate<F, T>,
    spec: Spec<F, T, RATE>,
    buf: Vec<WrapValue<F>>,
}

impl<F: PrimeFieldBits + FromUniformBytes<64>, const T: usize, const RATE: usize> ROCircuitTrait<F>
    for PoseidonChip<F, T, RATE>
{
    type Args = Spec<F, T, RATE>;
    type Config = MainGateConfig<T>;

    fn new(config: Self::Config, spec: Self::Args) -> Self {
        let main_gate: MainGate<F, T> = MainGate::new(config);
        Self {
            main_gate,
            spec,
            buf: Vec::new(),
        }
    }

    fn absorb_base(&mut self, base: WrapValue<F>) -> &mut Self {
        self.update(&[base])
    }

    fn absorb_point(&mut self, point: [WrapValue<F>; 2]) -> &mut Self {
        self.update(&point)
    }

    fn inspect(&mut self, scan: impl FnOnce(&[F])) -> &mut Self {
        if let Some(buf) = self
            .buf
            .iter()
            .map(|b| b.value().unwrap())
            .collect::<Option<Vec<_>>>()
        {
            scan(&buf)
        }
        self
    }

    fn squeeze_n_bits(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        num_bits: NonZeroUsize,
    ) -> Result<Vec<AssignedBit<F>>, Error> {
        let val = self.squeeze(ctx)?;
        let res = self.main_gate.le_num_to_bits(ctx, val, MAX_BITS)?;
        if res.len() >= num_bits.get() {
            Ok(res[..num_bits.get()].to_vec())
        } else {
            Ok(res)
        }
    }
}

impl<F: PrimeField + PrimeFieldBits, const T: usize, const RATE: usize> PoseidonChip<F, T, RATE> {
    pub fn new(config: MainGateConfig<T>, spec: Spec<F, T, RATE>) -> Self {
        let main_gate: MainGate<F, T> = MainGate::new(config);
        Self {
            main_gate,
            spec,
            buf: Vec::new(),
        }
    }

    pub fn next_state_val(
        state: [Value<F>; T],
        q_1: [F; T],
        q_5: [F; T],
        q_o: F,
        rc: F,
    ) -> Value<F> {
        let pow_5 = |v: Value<F>| {
            let v2 = v * v;
            v2 * v2 * v
        };
        let mut out = Value::known(rc);
        for ((s, q1), q5) in state.iter().zip(q_1).zip(q_5) {
            out = out + pow_5(*s) * Value::known(q5) + *s * Value::known(q1);
        }
        out * Value::known((-q_o).invert().unwrap())
    }

    pub fn pre_round(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        inputs: Vec<WrapValue<F>>,
        state_idx: usize,
        state: &[AssignedValue<F>; T],
    ) -> Result<AssignedValue<F>, Error> {
        assert!(inputs.len() <= RATE);
        let s_val = state[state_idx].value().copied();

        // TODO: add copy constraint
        let inputs = std::iter::once(Value::known(F::ZERO))
            .chain(inputs.into_iter().map(|v| v.value()))
            .chain(std::iter::once(Value::known(F::ONE)))
            .chain(std::iter::repeat(Value::known(F::ZERO)))
            .take(T)
            .collect::<Vec<_>>();
        let input_val = inputs[state_idx];

        let constants = self.spec.constants().start();
        let pre_constants = constants[0];
        let rc_val = pre_constants[state_idx];

        let out_val = s_val + input_val + Value::known(rc_val);

        let si = ctx.assign_advice(
            || "first round: state",
            self.main_gate.config().state[state_idx],
            s_val,
        )?;
        ctx.constrain_equal(state[state_idx].cell(), si.cell())?;

        ctx.assign_advice(
            || "pre_round: input",
            self.main_gate.config().input,
            input_val,
        )?;
        ctx.assign_fixed(
            || "pre_round: q_1",
            self.main_gate.config().q_1[state_idx],
            F::ONE,
        )?;
        ctx.assign_fixed(|| "pre_round: q_i", self.main_gate.config().q_i, F::ONE)?;
        ctx.assign_fixed(|| "pre_round: q_o", self.main_gate.config().q_o, -F::ONE)?;
        ctx.assign_fixed(|| "pre_round: rc", self.main_gate.config().rc, rc_val)?;
        let out = ctx.assign_advice(|| "pre_round: out", self.main_gate.config().out, out_val)?;

        ctx.next();
        Ok(out)
    }

    // round_idx \in [0; r_f - 1] indicates the round index of either first half full or second half full
    pub fn full_round(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        is_first_half_full: bool,
        round_idx: usize,
        state_idx: usize,
        state: &[AssignedCell<F, F>; T],
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut state_vals = [Value::known(F::ZERO); T];
        let q_1_vals = [F::ZERO; T];
        let mut q_5_vals = [F::ZERO; T];
        let q_o_val = -F::ONE;

        let r_f = self.spec.r_f() / 2;
        let constants = if is_first_half_full {
            self.spec.constants().start()
        } else {
            self.spec.constants().end()
        };
        let rcs = if is_first_half_full {
            constants[round_idx + 1]
        } else if round_idx < r_f - 1 {
            constants[round_idx]
        } else {
            [F::ZERO; T]
        };

        let mds = if is_first_half_full && round_idx == r_f - 1 {
            self.spec.mds_matrices().pre_sparse_mds().rows()
        } else {
            self.spec.mds_matrices().mds().rows()
        };
        let mds_row = mds[state_idx];

        let mut rc_val = F::ZERO;
        for (j, (mij, cj)) in mds_row.iter().zip(rcs).enumerate() {
            rc_val += *mij * cj;
            q_5_vals[j] = *mij;
            ctx.assign_fixed(
                || format!("full_round {}: q_5", round_idx),
                self.main_gate.config().q_5[j],
                q_5_vals[j],
            )?;
        }

        for (i, s) in state.iter().enumerate() {
            state_vals[i] = s.value().copied();
            let si = ctx.assign_advice(
                || format!("full_round {}: state", round_idx),
                self.main_gate.config().state[i],
                s.value().copied(),
            )?;
            ctx.constrain_equal(s.cell(), si.cell())?;
        }

        ctx.assign_fixed(
            || format!("full_round {}: rc", round_idx),
            self.main_gate.config().rc,
            rc_val,
        )?;
        ctx.assign_fixed(
            || format!("full_round {}: q_o", round_idx),
            self.main_gate.config().q_o,
            q_o_val,
        )?;
        let out_val = Self::next_state_val(state_vals, q_1_vals, q_5_vals, q_o_val, rc_val);
        let out = ctx.assign_advice(
            || format!("full_round {}: out", round_idx),
            self.main_gate.config().out,
            out_val,
        )?;
        ctx.next();
        Ok(out)
    }

    pub fn partial_round(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        round_idx: usize,
        state_idx: usize,
        state: &[AssignedValue<F>; T],
    ) -> Result<AssignedValue<F>, Error> {
        let mut state_vals = [Value::known(F::ZERO); T];
        let mut q_1_vals = [F::ZERO; T];
        let mut q_5_vals = [F::ZERO; T];
        let q_o_val = -F::ONE;

        let constants = self.spec.constants().partial();
        let rc = constants[round_idx];

        let sparse_mds = self.spec.mds_matrices().sparse_matrices();
        let row = sparse_mds[round_idx].row();
        let col_hat = sparse_mds[round_idx].col_hat();

        for (i, s) in state.iter().enumerate() {
            state_vals[i] = s.value().copied();
            let si = ctx.assign_advice(
                || format!("partial_round {}: state", round_idx),
                self.main_gate.config().state[i],
                s.value().copied(),
            )?;
            ctx.constrain_equal(s.cell(), si.cell())?;
        }

        let rc_val;
        if state_idx == 0 {
            q_5_vals[0] = row[0];
            ctx.assign_fixed(
                || format!("partial_round {}: q_5", round_idx),
                self.main_gate.config().q_5[0],
                q_5_vals[0],
            )?;
            rc_val = row[0] * rc;
            ctx.assign_fixed(
                || format!("partial_round {}: rc", round_idx),
                self.main_gate.config().rc,
                rc_val,
            )?;
            for j in 1..T {
                q_1_vals[j] = row[j];
                ctx.assign_fixed(
                    || format!("partial_round {}: q_1", round_idx),
                    self.main_gate.config().q_1[j],
                    q_1_vals[j],
                )?;
            }
        } else {
            q_5_vals[0] = col_hat[state_idx - 1];
            q_1_vals[state_idx] = F::ONE;
            ctx.assign_fixed(
                || format!("partial_round {}: q_5", round_idx),
                self.main_gate.config().q_5[0],
                q_5_vals[0],
            )?;
            ctx.assign_fixed(
                || format!("partial_round {}: q_1", round_idx),
                self.main_gate.config().q_1[state_idx],
                q_1_vals[state_idx],
            )?;
            rc_val = col_hat[state_idx - 1] * rc;
            ctx.assign_fixed(
                || format!("partial_round {}, rc", round_idx),
                self.main_gate.config().rc,
                rc_val,
            )?;
        }

        let out_val = Self::next_state_val(state_vals, q_1_vals, q_5_vals, -F::ONE, rc_val);
        ctx.assign_fixed(
            || format!("full_round {}: q_o", round_idx),
            self.main_gate.config().q_o,
            q_o_val,
        )?;
        let out = ctx.assign_advice(
            || format!("full_round {}: out", round_idx),
            self.main_gate.config().out,
            out_val,
        )?;
        ctx.next();
        Ok(out)
    }

    pub fn permutation(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        inputs: Vec<WrapValue<F>>,
        init_state: &[AssignedValue<F>; T],
    ) -> Result<[AssignedValue<F>; T], Error> {
        let mut state = Vec::new();
        for i in 0..T {
            let si = self.pre_round(ctx, inputs.clone(), i, init_state)?;
            state.push(si);
        }

        let r_f = self.spec.r_f() / 2;
        let r_p = self.spec.constants().partial().len();

        for round_idx in 0..r_f {
            let mut next_state = Vec::new();
            for state_idx in 0..T {
                let si = self.full_round(
                    ctx,
                    true,
                    round_idx,
                    state_idx,
                    state[..].try_into().unwrap(),
                )?;
                next_state.push(si);
            }
            state = next_state;
        }

        for round_idx in 0..r_p {
            let mut next_state = Vec::new();
            for state_idx in 0..T {
                let si =
                    self.partial_round(ctx, round_idx, state_idx, state[..].try_into().unwrap())?;
                next_state.push(si);
            }
            state = next_state;
        }

        for round_idx in 0..r_f {
            let mut next_state = Vec::new();
            for state_idx in 0..T {
                let si = self.full_round(
                    ctx,
                    false,
                    round_idx,
                    state_idx,
                    state[..].try_into().unwrap(),
                )?;
                next_state.push(si);
            }
            state = next_state;
        }
        let res: [AssignedValue<F>; T] = state.try_into().unwrap();
        Ok(res)
    }

    pub fn update(&mut self, inputs: &[WrapValue<F>]) -> &mut Self {
        self.buf.extend_from_slice(inputs);
        self
    }

    pub fn squeeze(&mut self, ctx: &mut RegionCtx<'_, F>) -> Result<AssignedValue<F>, Error> {
        //let buf = mem::take(&mut self.buf);
        let buf = self.buf.clone();
        if let Some(buf) = buf
            .iter()
            .map(|val| val.value().unwrap())
            .collect::<Option<Vec<F>>>()
        {
            debug!("On circuit input of hash: {buf:?}",);
        }

        let exact = buf.len() % RATE == 0;
        let state0: [F; T] = poseidon::State::default().words();

        let mut state: [AssignedValue<F>; T] = self
            .main_gate
            .config()
            .state
            .into_iter()
            .zip(state0.into_iter().map(Value::known))
            .map(|(state_column, state0_value)| {
                ctx.assign_advice(|| "initial state", state_column, state0_value)
            })
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .expect("Unreachable, because zip two arrays with same size");

        for chunk in buf.chunks(RATE) {
            state = self.permutation(ctx, chunk.to_vec(), &state)?;
        }

        if exact {
            state = self.permutation(ctx, Vec::new(), &state)?;
        }

        Ok(state[1].clone())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{Circuit, Column, ConstraintSystem, Instance},
    };
    use tracing_test::traced_test;

    use super::*;
    use crate::{
        create_and_verify_proof,
        halo2curves::{
            group::ff::FromUniformBytes,
            pasta::{EqAffine, Fp},
        },
        main_gate::MainGateConfig,
        poseidon::Spec,
        run_mock_prover_test,
    };

    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
        pconfig: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    struct TestCircuit<F: PrimeField + PrimeFieldBits> {
        inputs: Vec<WrapValue<F>>,
        num_bits: NonZeroUsize,
    }

    impl<F: PrimeField + PrimeFieldBits> TestCircuit<F> {
        fn new(inputs: Vec<F>, num_bits: NonZeroUsize) -> Self {
            Self {
                inputs: inputs
                    .into_iter()
                    .map(|v| Value::known(v).into())
                    .collect::<Vec<_>>(),
                num_bits,
            }
        }
    }

    impl<F: PrimeField + PrimeFieldBits + FromUniformBytes<64>> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: Vec::new(),
                num_bits: NonZeroUsize::new(1).unwrap(),
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let pconfig = MainGate::configure(meta);
            Self::Config { pconfig, instance }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let spec = Spec::<F, T, RATE>::new(R_F, R_P);
            let mut pchip = PoseidonChip::new(config.pconfig, spec);
            pchip.update(&self.inputs[..]);
            let output = layouter.assign_region(
                || "poseidon hash",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    let bits = pchip.squeeze_n_bits(ctx, self.num_bits)?;
                    pchip.main_gate.le_bits_to_num(ctx, &bits)
                },
            )?;
            layouter.constrain_instance(output.cell(), config.instance, 0)?;
            Ok(())
        }
    }

    #[traced_test]
    #[test]
    fn test_poseidon_circuit() {
        println!("-----running Poseidon Circuit-----");
        let mut inputs = Vec::new();
        let num_bits = NonZeroUsize::new(128).unwrap();
        for i in 0..5 {
            inputs.push(Fp::from(i as u64));
        }

        const K: u32 = 10;
        let circuit = TestCircuit::new(inputs, num_bits);

        let out_hash = Fp::from_str_vartime("277726250230731218669330566268314254439").unwrap();

        create_and_verify_proof!(IPA, K, circuit, &[&[out_hash]], EqAffine);
        println!("-----poseidon circuit works fine-----");
    }

    #[test]
    fn test_mock() {
        const K: u32 = 10;
        let mut inputs = Vec::new();
        let num_bits = NonZeroUsize::new(128).unwrap();
        for i in 0..5 {
            inputs.push(Fp::from(i as u64));
        }
        let circuit = TestCircuit::new(inputs, num_bits);
        // let out_hash = Fp::from_str_vartime("13037709793114148810823325920380362524528554380279235267325741570708489436263").unwrap();
        let out_hash = Fp::from_str_vartime("277726250230731218669330566268314254439").unwrap();
        let public_inputs = vec![vec![out_hash]];

        run_mock_prover_test!(K, circuit, public_inputs);
    }
}
