use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{self, Advice, Circuit, Column, ConstraintSystem, Instance, Selector},
    poly::Rotation,
};
use some_to_err::*;

use super::*;
use crate::{
    ff::{PrimeField, PrimeFieldBits},
    halo2curves::{
        bn256::{Fr, G1Affine},
        group::ff::FromUniformBytes,
    },
    nifs::{self, vanilla::VanillaFS},
    plonk::{
        PlonkStructure, PlonkTrace, RelaxedPlonkInstance, RelaxedPlonkTrace, RelaxedPlonkWitness,
    },
    table::CircuitRunner,
    util::create_ro,
};

#[derive(thiserror::Error, Debug)]
enum Error<C: CurveAffine> {
    #[error(transparent)]
    Nifs(#[from] nifs::vanilla::Error),
    #[error(transparent)]
    Plonk(#[from] plonk::Error),
    #[error("while verify: {errors:?}")]
    Verify {
        errors: Vec<(&'static str, crate::plonk::Error)>,
    },
    #[error("not equal: {from_verify:?} != {from_prove:?}")]
    VerifyProveNotMatch {
        from_verify: Box<RelaxedPlonkInstance<C>>,
        from_prove: Box<RelaxedPlonkInstance<C>>,
    },
}
impl<C: CurveAffine> Error<C> {
    fn check_equality(
        from_verify: &RelaxedPlonkInstance<C>,
        from_prove: &RelaxedPlonkInstance<C>,
    ) -> Result<(), Self> {
        from_verify
            .ne(from_prove)
            .then(|| Self::VerifyProveNotMatch {
                from_verify: Box::new(from_verify.clone()),
                from_prove: Box::new(from_prove.clone()),
            })
            .err_or(())
    }
}

fn prepare_trace<C, F1, F2, CT>(
    K: u32,
    circuit1: CT,
    circuit2: CT,
    public_inputs1: Vec<F1>,
    public_inputs2: Vec<F1>,
    pp_digest: C,
) -> Result<
    (
        CommitmentKey<C>,
        PlonkStructure<F1>,
        PlonkTrace<C>,
        PlonkTrace<C>,
    ),
    Error<C>,
>
where
    C: CurveAffine<ScalarExt = F1, Base = F2>,
    F1: PrimeField,
    F2: PrimeFieldBits + FromUniformBytes<64>,
    CT: Circuit<F1>,
{
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    let td1 = CircuitRunner::new(K, circuit1, public_inputs1.clone());
    let num_lookup = td1.cs.lookups().len();
    let p1 = smallest_power(td1.cs.num_advice_columns() + 5 * num_lookup, K);
    let p2 = smallest_power(td1.cs.num_selectors + td1.cs.num_fixed_columns(), K);
    let ck = CommitmentKey::<C>::setup(p1.max(p2), b"prepare_trace");

    let S = td1.try_collect_plonk_structure()?;
    let W1 = td1.try_collect_witness()?;

    let td2 = CircuitRunner::new(K, circuit2, public_inputs2.clone());
    let W2 = td2.try_collect_witness()?;

    let mut ro_nark_prepare = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_nark_decider = create_ro::<C::Base, T, RATE, R_F, R_P>();

    let (pp, _vp) = VanillaFS::setup_params(pp_digest, S.clone())?;

    let pair1 =
        VanillaFS::generate_plonk_trace(&ck, &public_inputs1, &W1, &pp, &mut ro_nark_prepare)?;
    let pair1_relaxed = pair1.to_relax(S.k);

    let pair2 =
        VanillaFS::generate_plonk_trace(&ck, &public_inputs2, &W2, &pp, &mut ro_nark_prepare)?;
    let pair2_relaxed = pair2.to_relax(S.k);

    let mut errors = Vec::new();

    if let Err(err) = S.is_sat(&ck, &mut ro_nark_decider, &pair1.u, &pair1.w) {
        errors.push(("is_sat_pair1", err));
    }
    if let Err(err) = S.is_sat_perm(&pair1_relaxed.U, &pair1_relaxed.W) {
        errors.push(("is_sat_perm_pair1", err));
    }
    if let Err(err) = S.is_sat(&ck, &mut ro_nark_decider, &pair2.u, &pair2.w) {
        errors.push(("is_sat_pair2", err));
    }
    if let Err(err) = S.is_sat_perm(&pair2_relaxed.U, &pair2_relaxed.W) {
        errors.push(("is_sat_perm_pair2", err));
    }

    if errors.is_empty() {
        Ok((ck, S, pair1, pair2))
    } else {
        Err(Error::Verify { errors })
    }
}

/// this function will fold two plonk witness-instance pairs consecutively
/// it folds the first instance into a default relaxed plonk instance to get folded (f_U, f_W)
/// next it folds the second instance into the first folded (f_U, f_W)
/// there are several things to be checked: whether two such instances satisfy plonk relation
/// (i.e. is_sat), whether two such folded instance satisfy relaxed plonk relation (i.e.
/// is_sat_relax)
/// We have to check:
/// (1) each of the two individual witness-instance pairs satisfy custom gates relation as well
/// as copy constrains relation (i.e. permutation relation)
/// (2) the first folded witness-instance pair satisfies the relaxed polynomial relation and
/// copy constrains relation
/// (3) the second folded witness-instance pair satisfies the relaxed polynomial relation  and
/// copy constrains relation
fn fold_instances<C, F1, F2>(
    ck: &CommitmentKey<C>,
    S: &PlonkStructure<F1>,
    pair1: PlonkTrace<C>,
    pair2: PlonkTrace<C>,
    pp_digest: C,
) -> Result<(), Error<C>>
where
    C: CurveAffine<ScalarExt = F1, Base = F2>,
    F1: PrimeField,
    F2: PrimeFieldBits + FromUniformBytes<64>,
{
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    let mut f_U = RelaxedPlonkInstance::new(S.num_io, S.num_challenges, S.round_sizes.len());
    let mut f_W = RelaxedPlonkWitness::new(S.k, &S.round_sizes);

    let mut ro_nark_verifier = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_acc_prover = create_ro::<C::Base, T, RATE, R_F, R_P>();
    let mut ro_acc_verifier = create_ro::<C::Base, T, RATE, R_F, R_P>();

    let (pp, vp) = VanillaFS::setup_params(pp_digest, S.clone())?;

    let pair1 = [pair1];
    let (RelaxedPlonkTrace { U: U_from_prove, W }, cross_term_commits) = VanillaFS::prove(
        ck,
        &pp,
        &mut ro_acc_prover,
        &RelaxedPlonkTrace {
            U: f_U.clone(),
            W: f_W.clone(),
        },
        &pair1,
    )?;

    let U_from_verify = VanillaFS::verify(
        &vp,
        &mut ro_nark_verifier,
        &mut ro_acc_verifier,
        &f_U,
        &pair1.map(|p| p.u),
        &cross_term_commits,
    )?;
    Error::check_equality(&U_from_verify, &U_from_prove)?;

    f_U = U_from_verify;
    f_W = W;

    let mut errors = Vec::new();
    if let Err(err) = S.is_sat_relaxed(ck, &f_U, &f_W) {
        errors.push(("is_sat_relaxed 1", err));
    }
    if let Err(err) = S.is_sat_perm(&f_U, &f_W) {
        errors.push(("is_sat_perm 1", err));
    }

    let pair2 = [pair2];
    let (
        RelaxedPlonkTrace {
            U: U_from_prove,
            W: _W,
        },
        cross_term_commits,
    ) = VanillaFS::prove(
        ck,
        &pp,
        &mut ro_acc_prover,
        &RelaxedPlonkTrace {
            U: f_U.clone(),
            W: f_W,
        },
        &pair2,
    )?;

    let U_from_verify = VanillaFS::verify(
        &vp,
        &mut ro_nark_verifier,
        &mut ro_acc_verifier,
        &f_U,
        &pair2.map(|p| p.u),
        &cross_term_commits,
    )?;
    assert_eq!(U_from_prove, U_from_verify);

    f_U = U_from_verify;
    f_W = _W;

    if let Err(err) = S.is_sat_relaxed(ck, &f_U, &f_W) {
        errors.push(("is_sat_relaxed 2", err));
    }
    if let Err(err) = S.is_sat_perm(&f_U, &f_W) {
        errors.push(("is_sat_perm 2", err));
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(Error::Verify { errors })
    }
}

/// calculate smallest w such that 2^w >= n*(2^K)
fn smallest_power(n: usize, K: u32) -> usize {
    let n_f64 = n as f64;
    let mul_res = n_f64 * (2f64.powi(K as i32));
    let log_result = mul_res.log2().ceil();
    log_result as usize
}

// test with single custom gate without lookup
mod zero_round_test {
    use tracing_test::traced_test;

    use super::*;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};

    const T: usize = 3;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
        pconfig: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    struct TestCircuit<F: PrimeField> {
        inputs: Vec<F>,
        r: F,
    }

    impl<F: PrimeField> TestCircuit<F> {
        fn new(inputs: Vec<F>, r: F) -> Self {
            Self { inputs, r }
        }
    }

    impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: Vec::new(),
                r: F::ZERO,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            Self::Config {
                pconfig: MainGate::configure(meta),
                instance,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), plonk::Error> {
            let pchip = MainGate::new(config.pconfig);
            let output = layouter.assign_region(
                || "test",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    pchip.random_linear_combination(ctx, self.inputs.clone(), self.r)
                },
            )?;
            layouter.constrain_instance(output.cell(), config.instance, 0)?;
            Ok(())
        }
    }

    #[traced_test]
    #[test]
    fn test_nifs() -> Result<(), Error<G1Affine>> {
        const K: u32 = 4;
        let inputs1 = (1..10).map(Fr::from).collect();
        let inputs2 = (2..11).map(Fr::from).collect();
        let circuit1 = TestCircuit::new(inputs1, Fr::from_u128(2));
        let output1 = Fr::from_u128(4097);
        let public_inputs1 = vec![output1];

        let circuit2 = TestCircuit::new(inputs2, Fr::from_u128(3));
        let output2 = Fr::from_u128(93494);
        let public_inputs2 = vec![output2];

        let (ck, S, pair1, pair2) = prepare_trace(
            K,
            circuit1,
            circuit2,
            public_inputs1,
            public_inputs2,
            G1Affine::default(),
        )?;
        fold_instances(&ck, &S, pair1, pair2, G1Affine::default())
    }
}

// test multiple gates without lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
mod one_round_test {
    use tracing_test::traced_test;

    use super::*;

    #[derive(Clone)]
    struct Number<F: PrimeField>(AssignedCell<F, F>);

    #[derive(Debug, Clone)]
    struct FiboConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        selector: Selector,
        instance: Column<Instance>,
    }

    struct FiboChip<F: PrimeField> {
        config: FiboConfig,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField> FiboChip<F> {
        fn construct(config: FiboConfig) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: [Column<Advice>; 2],
            selector: Selector,
            instance: Column<Instance>,
        ) -> FiboConfig {
            let a = advice[0];
            let b = advice[1];

            meta.enable_equality(b);
            meta.enable_equality(instance);

            meta.create_gate("fibo-block", |meta| {
                let s = meta.query_selector(selector);
                let a1 = meta.query_advice(a, Rotation::prev());
                let b1 = meta.query_advice(b, Rotation::prev());
                let a2 = meta.query_advice(a, Rotation::cur());
                let b2 = meta.query_advice(b, Rotation::cur());
                vec![
                    s.clone() * (a2.clone() - b1.clone() - a1),
                    s * (b2 - a2 - b1),
                ]
            });

            FiboConfig {
                a,
                b,
                selector,
                instance,
            }
        }

        fn load(
            &self,
            mut layouter: impl Layouter<F>,
            a: F,
            b: F,
            nrows: usize,
        ) -> Result<(Number<F>, Number<F>), plonk::Error> {
            layouter.assign_region(
                || "entire block",
                |mut region| {
                    // assign first row
                    let mut a = region
                        .assign_advice(|| "a", self.config.a, 0, || Value::known(a))
                        .map(Number)?;

                    let mut b = region
                        .assign_advice(|| "b", self.config.b, 0, || Value::known(b))
                        .map(Number)?;

                    for idx in 1..nrows {
                        self.config.selector.enable(&mut region, idx)?;
                        let a2 = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));
                        let b2 = a2.and_then(|a| b.0.value().map(|b| a + *b));

                        a = region
                            .assign_advice(|| "a", self.config.a, idx, || a2)
                            .map(Number)?;

                        b = region
                            .assign_advice(|| "b", self.config.b, idx, || b2)
                            .map(Number)?;
                    }

                    Ok((a, b))
                },
            )
        }

        fn expose_public(
            &self,
            mut layouter: impl Layouter<F>,
            num: Number<F>,
            row: usize,
        ) -> Result<(), plonk::Error> {
            layouter.constrain_instance(num.0.cell(), self.config.instance, row)
        }
    }

    #[derive(Default)]
    struct FiboCircuit<F> {
        a: F,
        b: F,
        num: usize,
    }

    impl<F: PrimeField> Circuit<F> for FiboCircuit<F> {
        type Config = FiboConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = [meta.advice_column(), meta.advice_column()];
            let selector = meta.selector();
            let instance = meta.instance_column();
            FiboChip::configure(meta, advice, selector, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), plonk::Error> {
            let chip = FiboChip::construct(config);
            let nrows = (self.num + 1) / 2;
            let (_, b) = chip.load(layouter.namespace(|| "block"), self.a, self.b, nrows)?;
            chip.expose_public(layouter.namespace(|| "expose b"), b, 0)?;
            Ok(())
        }
    }

    fn get_fibo_seq(a: u64, b: u64, num: usize) -> Vec<u64> {
        let mut seq = vec![0; num];
        seq[0] = a;
        seq[1] = b;
        for i in 2..num {
            seq[i] = seq[i - 1] + seq[i - 2];
        }
        seq
    }

    #[traced_test]
    #[test]
    fn test_nifs() -> Result<(), Error<G1Affine>> {
        const K: u32 = 4;
        const SIZE: usize = 16;
        // circuit 1
        let seq = get_fibo_seq(1, 1, SIZE);
        let circuit1 = FiboCircuit {
            a: Fr::from(seq[0]),
            b: Fr::from(seq[1]),
            num: SIZE,
        };
        let public_inputs1 = vec![Fr::from(seq[SIZE - 1])];

        // circuit 2
        let seq = get_fibo_seq(2, 3, SIZE);
        let circuit2 = FiboCircuit {
            a: Fr::from(seq[0]),
            b: Fr::from(seq[1]),
            num: SIZE,
        };
        let public_inputs2 = vec![Fr::from(seq[SIZE - 1])];

        let (ck, S, pair1, pair2) = prepare_trace(
            K,
            circuit1,
            circuit2,
            public_inputs1,
            public_inputs2,
            G1Affine::default(),
        )?;
        fold_instances(&ck, &S, pair1, pair2, G1Affine::default())
    }
}

// test vector lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
mod three_rounds_test {
    use halo2_proofs::{circuit::Chip, plonk::TableColumn};
    use num_bigint::BigUint as BigUintRaw;
    use tracing_test::traced_test;

    use super::*;

    pub fn f_to_u64<F: PrimeField>(f: &F) -> u64 {
        BigUintRaw::from_bytes_le(f.to_repr().as_ref())
            .try_into()
            .unwrap()
    }

    #[derive(Clone, Debug)]
    struct Number<F: PrimeField>(AssignedCell<F, F>);

    #[derive(Debug, Clone)]
    struct FiboConfig {
        advice: [Column<Advice>; 3],
        s_add: Selector,
        s_xor: Selector,
        xor_table: [TableColumn; 3],
    }

    struct FiboChip<F: PrimeField> {
        config: FiboConfig,
        _marker: PhantomData<F>,
    }

    // ANCHOR: chip-impl
    impl<F: PrimeField> Chip<F> for FiboChip<F> {
        type Config = FiboConfig;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }
    // ANCHOR_END: chip-impl

    impl<F: PrimeField> FiboChip<F> {
        fn construct(config: FiboConfig) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: [Column<Advice>; 3],
            selector: [Selector; 2],
        ) -> FiboConfig {
            let s_add = selector[0];
            let s_xor = selector[1];

            let xor_table = [
                meta.lookup_table_column(),
                meta.lookup_table_column(),
                meta.lookup_table_column(),
            ];

            meta.enable_equality(advice[0]);
            meta.enable_equality(advice[1]);
            meta.enable_equality(advice[2]);

            meta.lookup("xor", |meta| {
                let s_xor = meta.query_selector(s_xor);
                let lhs = meta.query_advice(advice[0], Rotation::cur());
                let rhs = meta.query_advice(advice[1], Rotation::cur());
                let out = meta.query_advice(advice[2], Rotation::cur());
                vec![
                    (s_xor.clone() * lhs, xor_table[0]),
                    (s_xor.clone() * rhs, xor_table[1]),
                    (s_xor * out, xor_table[2]),
                ]
            });

            meta.create_gate("add", |meta| {
                let s_add = meta.query_selector(s_add);
                let lhs = meta.query_advice(advice[0], Rotation::cur());
                let rhs = meta.query_advice(advice[1], Rotation::cur());
                let out = meta.query_advice(advice[2], Rotation::cur());
                vec![s_add * (lhs + rhs - out)]
            });

            FiboConfig {
                advice,
                s_add,
                s_xor,
                xor_table,
            }
        }

        fn load_private(
            &self,
            mut layouter: impl Layouter<F>,
            a: F,
            b: F,
            c: F,
        ) -> Result<(Number<F>, Number<F>, Number<F>), plonk::Error> {
            let config = self.config();

            layouter.assign_region(
                || "private",
                |mut region| {
                    let a_num = region
                        .assign_advice(|| "a", config.advice[0], 0, || Value::known(a))
                        .map(Number)?;

                    let b_num = region
                        .assign_advice(|| "b", config.advice[1], 0, || Value::known(b))
                        .map(Number)?;

                    let c_num = region
                        .assign_advice(|| "c", config.advice[2], 0, || Value::known(c))
                        .map(Number)?;

                    Ok((a_num, b_num, c_num))
                },
            )
        }

        fn add(
            &self,
            mut layouter: impl Layouter<F>,
            a: &Number<F>,
            b: &Number<F>,
        ) -> Result<Number<F>, plonk::Error> {
            let config = self.config();
            layouter.assign_region(
                || "add",
                |mut region| {
                    config.s_add.enable(&mut region, 0)?;

                    a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                    b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                    let value = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));

                    region
                        .assign_advice(|| "out", config.advice[2], 0, || value)
                        .map(Number)
                },
            )
        }

        fn xor(
            &self,
            mut layouter: impl Layouter<F>,
            a: &Number<F>,
            b: &Number<F>,
        ) -> Result<Number<F>, plonk::Error> {
            let config = self.config();
            layouter.assign_region(
                || "xor",
                |mut region| {
                    config.s_xor.enable(&mut region, 0)?;

                    a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                    b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                    let value = a.0.value().and_then(|a| {
                        b.0.value().map(|b| {
                            let a_val = f_to_u64(a);
                            let b_val = f_to_u64(b);
                            F::from(a_val ^ b_val)
                        })
                    });

                    region
                        .assign_advice(|| "out", config.advice[2], 0, || value)
                        .map(Number)
                },
            )
        }

        fn load_table(&self, mut layouter: impl Layouter<F>) -> Result<(), plonk::Error> {
            layouter.assign_table(
                || "xor",
                |mut table| {
                    let mut idx = 0;
                    for lhs in 0..5 {
                        for rhs in 0..5 {
                            table.assign_cell(
                                || "lhs",
                                self.config.xor_table[0],
                                idx,
                                || Value::known(F::from(lhs)),
                            )?;
                            table.assign_cell(
                                || "rhs",
                                self.config.xor_table[1],
                                idx,
                                || Value::known(F::from(rhs)),
                            )?;
                            table.assign_cell(
                                || "lhs ^ rhs",
                                self.config.xor_table[2],
                                idx,
                                || Value::known(F::from(lhs ^ rhs)),
                            )?;
                            idx += 1;
                        }
                    }
                    Ok(())
                },
            )
        }
    }

    #[derive(Default)]
    struct FiboCircuit<F> {
        a: F,
        b: F,
        c: F,
        num: usize,
    }

    impl<F: PrimeField> Circuit<F> for FiboCircuit<F> {
        type Config = FiboConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];
            let selector = [meta.selector(), meta.complex_selector()];
            FiboChip::configure(meta, advice, selector)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), plonk::Error> {
            let chip = FiboChip::construct(config);
            let (mut a, mut b, mut c) =
                chip.load_private(layouter.namespace(|| "first row"), self.a, self.b, self.c)?;
            for _ in 3..self.num {
                let xor = chip.xor(layouter.namespace(|| "xor"), &b, &c)?;
                let new_c = chip.add(layouter.namespace(|| "add"), &a, &xor)?;
                a = b;
                b = c;
                c = new_c;
            }
            chip.load_table(layouter.namespace(|| "lookup table"))?;
            Ok(())
        }
    }

    fn get_sequence(a: u64, b: u64, c: u64, num: usize) -> Vec<u64> {
        let mut seq = vec![0; num];
        seq[0] = a;
        seq[1] = b;
        seq[2] = c;
        for i in 3..num {
            seq[i] = seq[i - 3] + (seq[i - 2] ^ seq[i - 1]);
        }
        seq
    }

    #[traced_test]
    #[test]
    fn test_nifs() -> Result<(), Error<G1Affine>> {
        const K: u32 = 5;
        let num = 7;

        // circuit 1
        let seq = get_sequence(1, 3, 2, num);
        let circuit1 = FiboCircuit {
            a: Fr::from(seq[0]),
            b: Fr::from(seq[1]),
            c: Fr::from(seq[2]),
            num,
        };

        // circuit 2
        let seq = get_sequence(3, 2, 2, num);
        let circuit2 = FiboCircuit {
            a: Fr::from(seq[0]),
            b: Fr::from(seq[1]),
            c: Fr::from(seq[2]),
            num,
        };

        let (ck, S, pair1, pair2) =
            prepare_trace(K, circuit1, circuit2, vec![], vec![], G1Affine::default())?;
        fold_instances(&ck, &S, pair1, pair2, G1Affine::default())
    }
}
