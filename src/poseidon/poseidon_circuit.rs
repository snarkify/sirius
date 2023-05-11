use poseidon::{self, Spec};
use halo2_proofs::{
    circuit::{Value, AssignedCell},
    plonk::{Advice, ConstraintSystem, Column, 
        Fixed, Expression, Error},
    poly::Rotation};
use ff::PrimeField;
use std::marker::PhantomData;
use std::mem;
use std::convert::TryInto;
use crate::standard_gate::RegionCtx;

#[derive(Clone, Debug)]
pub struct PoseidonConfig<F: PrimeField, const T: usize, const RATE: usize> {
    state: [Column<Advice>; T],
    input: Column<Advice>,
    out: Column<Advice>,
    // for linear term
    q_1: [Column<Fixed>; T],
    // for quintic term
    q_5: [Column<Fixed>; T],
    q_o: Column<Fixed>,
    rc: Column<Fixed>,
    _mark: PhantomData<F>,
}

#[derive(Debug)]
pub struct PoseidonChip<F: PrimeField, const T: usize, const RATE: usize> {
    config: PoseidonConfig<F, T, RATE>,
    spec: Spec<F, T, RATE>,
    buf: Vec<F>,
}

impl<F: PrimeField, const T: usize, const RATE: usize> PoseidonChip<F,T,RATE> {
    pub fn new(config: PoseidonConfig<F, T, RATE>, spec: Spec<F,T,RATE>) -> Self {
        Self {
            config,
            spec,
            buf: Vec::new()
        }
    }

    pub fn next_state_val(state: [Value<F>; T], q_1: [F; T], q_5: [F; T], q_o: F, rc: F) -> Value<F> {
        let pow_5 = |v: Value<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2 * v
        };
        let mut out = Value::known(rc);
        for ((s, q1), q5) in state.iter().zip(q_1).zip(q_5) {
            out = out + pow_5(*s) * Value::known(q5) + *s * Value::known(q1);
        }
        out * Value::known((-q_o).invert().unwrap())
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: &mut (impl Iterator<Item = Column<Advice>> + Clone),
        fix_cols: &mut (impl Iterator<Item = Column<Fixed>> + Clone),
    ) -> PoseidonConfig<F, T, RATE> {
        
        let state = [0; T].map(|_| adv_cols.next().unwrap());
        let input = adv_cols.next().unwrap();
        let out = adv_cols.next().unwrap();
        let q_1 = [0; T].map(|_| fix_cols.next().unwrap());
        let q_5 = [0; T].map(|_| fix_cols.next().unwrap());
        let q_o = fix_cols.next().unwrap();
        let rc = fix_cols.next().unwrap();

        state.map(|s| {
            meta.enable_equality(s);
        });
        meta.enable_equality(out);

        let pow_5 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2 * v
        };

        meta.create_gate("sum_i(q_1[i]*s[i]) + sum_i(q_5[i]*s[i]^5) + rc + q_o*out=0", |meta|{
            let state = state.into_iter().map(|s| meta.query_advice(s, Rotation::cur())).collect::<Vec<_>>();
            let input = meta.query_advice(input, Rotation::cur());
            let out = meta.query_advice(out, Rotation::cur());
            let q_1 = q_1.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_5 = q_5.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_o = meta.query_fixed(q_o, Rotation::cur());
            let rc = meta.query_fixed(rc, Rotation::cur());
            let res = state.into_iter().zip(q_1).zip(q_5).map(|((w, q1), q5)| {
                q1 * w.clone()  +  q5 * pow_5(w)
            }).fold(input + rc +  q_o * out, |acc, item| {
                acc + item
            });
            vec![res]
        });

        PoseidonConfig {
            state,
            input,
            out,
            q_1,
            q_5,
            q_o,
            rc,
            _mark: PhantomData,
        }
    }

    pub fn first_round(&self, ctx: &mut RegionCtx<'_, F>, inputs: Vec<F>, state_idx: usize, state: Option<[AssignedCell<F, F>; T]>) -> Result<AssignedCell<F, F>, Error> {
        assert!(inputs.len() <= RATE); 
        let mut s_cell = None;
        let s_val = match state {
            Some(s) => {
                s_cell = Some(s[state_idx].cell());
                s[state_idx].value().copied()
            }
            None => {
                ctx.reset();
                Value::known(F::ZERO)
            }
        };

        let inputs = std::iter::once(F::ZERO).chain(inputs.into_iter())
        .chain(std::iter::once(F::ONE))
        .chain(std::iter::repeat(F::ZERO))
        .take(T).collect::<Vec<_>>();
        let input_val = Value::known(inputs[state_idx]);

        let constants = self.spec.constants().start();
        let pre_constants = constants[0];
        let rc_val = pre_constants[state_idx];

        let out_val = input_val + Value::known(rc_val);

        let si = ctx.assign_advice(||"first round: state", self.config.state[state_idx], s_val)?;
        if s_cell.is_some() {
            ctx.constrain_equal(s_cell.unwrap(), si.cell())?;
        }

        ctx.assign_advice(||"first round: input", self.config.input, input_val)?;
        ctx.assign_fixed(||"first round: q_1", self.config.q_1[state_idx], F::ONE)?;
        ctx.assign_fixed(||"first round: q_o", self.config.q_o, -F::ONE)?;
        ctx.assign_fixed(||"first round: rc", self.config.rc, rc_val)?;
        let out = ctx.assign_advice(||"first round: out", self.config.out, out_val)?;
    
        ctx.next();
        Ok(out)
    }

    // round_idx \in [0; r_f - 1] indicates the round index of either first half full or second half full
    pub fn full_round(&self, ctx: &mut RegionCtx<'_, F>, is_first_half_full: bool, round_idx: usize, state_idx: usize, state: &[AssignedCell<F,F>; T]) -> Result<AssignedCell<F,F>,Error> {
        let mut state_vals = [Value::known(F::ZERO); T];
        let q_1_vals = [F::ZERO; T];
        let mut q_5_vals = [F::ZERO; T];
        let q_o_val = -F::ONE;

        let r_f = self.spec.r_f() / 2;
        let constants = if is_first_half_full { self.spec.constants().start() } else { self.spec.constants().end() };
        let rcs = if is_first_half_full { constants[round_idx + 1] } else if round_idx < r_f - 1 { constants[round_idx] } else { [F::ZERO; T] };

        let mds = if is_first_half_full && round_idx == r_f - 1  { self.spec.mds_matrices().pre_sparse_mds().rows() } else { self.spec.mds_matrices().mds().rows() };
        let mds_row = mds[state_idx];


        let mut rc_val = F::ZERO;
        for (j, (mij, cj)) in mds_row.iter().zip(rcs).enumerate() {
            rc_val = rc_val + *mij * cj;
            q_5_vals[j] = *mij;
            ctx.assign_fixed(||format!("full_round {}: q_5", round_idx), self.config.q_5[j], q_5_vals[j])?;
        }

        for (i, s) in state.iter().enumerate() {
            state_vals[i] = s.value().copied();
            let si = ctx.assign_advice(||format!("full_round {}: state", round_idx), self.config.state[i], s.value().copied())?;
            ctx.constrain_equal(s.cell(), si.cell())?;
        }

        ctx.assign_fixed(||format!("full_round {}: rc", round_idx), self.config.rc, rc_val)?;
        ctx.assign_fixed(||format!("full_round {}: q_o", round_idx), self.config.q_o, q_o_val)?;
        let out_val = Self::next_state_val(state_vals, q_1_vals, q_5_vals, q_o_val, rc_val);
        let out = ctx.assign_advice(||format!("full_round {}: out", round_idx), self.config.out, out_val)?;
        ctx.next();
        Ok(out)
    }

    pub fn partial_round(&self, ctx: &mut RegionCtx<'_, F>, round_idx: usize, state_idx: usize, state: &[AssignedCell<F, F>; T]) -> Result<AssignedCell<F, F>, Error> {
        let mut state_vals = [Value::known(F::ZERO); T];
        let mut q_1_vals = [F::ZERO; T];
        let mut q_5_vals = [F::ZERO; T];
        let q_o_val = -F::ONE;

        let constants =  self.spec.constants().partial(); 
        let rc = constants[round_idx];

        let sparse_mds = self.spec.mds_matrices().sparse_matrices();
        let row = sparse_mds[round_idx].row();
        let col_hat = sparse_mds[round_idx].col_hat();

        for (i, s) in state.iter().enumerate() {
            state_vals[i] = s.value().copied();
            let si = ctx.assign_advice(||format!("partial_round {}: state", round_idx), self.config.state[i], s.value().copied())?;
            ctx.constrain_equal(s.cell(), si.cell())?;
        }

        let rc_val;
        if state_idx == 0 {
            q_5_vals[0] = row[0];
            ctx.assign_fixed(||format!("partial_round {}: q_5", round_idx), self.config.q_5[0], q_5_vals[0])?;
            rc_val = row[0] * rc;
            ctx.assign_fixed(||format!("partial_round {}: rc", round_idx), self.config.rc, rc_val)?;
            for j in 1..T {
                q_1_vals[j] = row[j];
                ctx.assign_fixed(||format!("partial_round {}: q_1", round_idx), self.config.q_1[j], q_1_vals[j])?;
            }
        } else {
            q_1_vals[0] = col_hat[state_idx - 1];
            q_1_vals[state_idx] = F::ONE;
            ctx.assign_fixed(||format!("partial_round {}: q_5", round_idx), self.config.q_1[0], q_1_vals[0])?;
            ctx.assign_fixed(||format!("partial_round {}: q_5", round_idx), self.config.q_1[0], q_1_vals[0])?;
            rc_val = col_hat[state_idx - 1] * rc;
            ctx.assign_fixed(||format!("partial_round {}, rc", round_idx), self.config.rc, rc_val)?;
        }

        let out_val = Self::next_state_val(state_vals, q_1_vals, q_5_vals, -F::ONE, rc_val);
        ctx.assign_fixed(||format!("full_round {}: q_o", round_idx), self.config.q_o, q_o_val)?;
        let out = ctx.assign_advice(||format!("full_round {}: out", round_idx), self.config.out, out_val)?;
        ctx.next();
        Ok(out)
    }

    pub fn permutation(&self, ctx: &mut RegionCtx<'_, F>, inputs: Vec<F>, init_state: Option<[AssignedCell<F, F>; T]>) -> Result<[AssignedCell<F, F>; T], Error> {
        let mut state = Vec::new();
        for i in 0..T {
            let si = self.first_round(ctx, inputs.clone(), i, init_state.clone())?;
            state.push(si);
        }

        let r_f = self.spec.r_f() / 2;
        let r_p = self.spec.constants().partial().len();

        for round_idx in 0..r_f {
            let mut next_state = Vec::new();
            for state_idx in 0..T {
                let si = self.full_round(ctx, true, round_idx, state_idx, state[..].try_into().unwrap())?;
                next_state.push(si);
            }
            state = next_state;
        }

        for round_idx in 0..r_p {
            let mut next_state = Vec::new();
            for  state_idx in 0..T {
                let si = self.partial_round(ctx, round_idx, state_idx, state[..].try_into().unwrap())?;
                next_state.push(si);
            }
            state = next_state;
        }

        for round_idx in 0..r_f {
            let mut next_state = Vec::new();
            for  state_idx in 0..T {
                let si = self.full_round(ctx, false, round_idx, state_idx, state[..].try_into().unwrap())?;
                next_state.push(si);
            }
            state = next_state;
        }
        let res: [AssignedCell<F, F>; T] = state.try_into().unwrap();
        Ok(res)
    }

    pub fn update(&mut self, inputs: Vec<F>) {
        self.buf.extend(inputs)
    }

    pub fn squeeze(&mut self, ctx: &mut RegionCtx<'_, F>) -> Result<AssignedCell<F, F>, Error> {
        let buf = mem::take(&mut self.buf);
        let exact = buf.len() % RATE == 0;
        let mut state = None;
        for chunk in buf.chunks(RATE) {
            let next_state = self.permutation(ctx, chunk.to_vec(), state)?;
            state = Some(next_state);
        }
        if exact {
            let next_state = self.permutation(ctx, Vec::new(), state)?;
            state = Some(next_state);
        }

        let res = state.clone().unwrap();
        Ok(res[1].clone())
    }
}
