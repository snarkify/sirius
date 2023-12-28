use super::*;
use crate::util::create_ro;
use ff::PrimeField;
use halo2curves::group::ff::FromUniformBytes;

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
fn fold_instances<
    C: CurveAffine<ScalarExt = F1, Base = F2>,
    F1: PrimeField,
    F2: PrimeField + FromUniformBytes<64>,
>(
    ck: &CommitmentKey<C>,
    td1: &TableData<F1>,
    td2: &TableData<F1>,
) -> Result<(), NIFSError> {
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 4;
    const R_P: usize = 3;

    let S = td1.plonk_structure(ck);
    let mut f_U =
        RelaxedPlonkInstance::new(td1.instance.len(), S.num_challenges, S.round_sizes.len());
    let mut f_W = RelaxedPlonkWitness::new(td1.k, &S.round_sizes);
    let mut ro_nark_prover = create_ro::<C, F2, T, RATE, R_F, R_P>();
    let mut ro_nark_prepare = create_ro::<C, F2, T, RATE, R_F, R_P>();
    let mut ro_nark_verifier = create_ro::<C, F2, T, RATE, R_F, R_P>();
    let mut ro_nark_decider = create_ro::<C, F2, T, RATE, R_F, R_P>();
    let (U1, W1) = td1
        .run_sps_protocol(ck, &mut ro_nark_prepare, S.num_challenges)
        .unwrap();
    let res = S.is_sat(ck, &mut ro_nark_decider, &U1, &W1);
    assert!(res.is_ok());

    let mut ro_acc_prover = create_ro::<C, F2, T, RATE, R_F, R_P>();
    let mut ro_acc_verifier = create_ro::<C, F2, T, RATE, R_F, R_P>();
    let (nifs, (_U, W)) =
        NIFS::prove(ck, &mut ro_nark_prover, &mut ro_acc_prover, td1, &f_U, &f_W)?;
    let U = nifs
        .verify(&mut ro_nark_verifier, &mut ro_acc_verifier, &S, f_U, U1)
        .unwrap();
    assert_eq!(U, _U);

    f_U = U;
    f_W = W;
    let res = S.is_sat_relaxed(ck, &f_U, &f_W);
    assert!(res.is_ok());
    //    let perm_res = S.is_sat_perm(&f_U, &f_W);
    //    assert!(perm_res.is_ok());

    let (U1, W1) = td2
        .run_sps_protocol(ck, &mut ro_nark_prepare, S.num_challenges)
        .unwrap();
    let res = S.is_sat(ck, &mut ro_nark_decider, &U1, &W1);
    assert!(res.is_ok());

    let (nifs, (_U, _W)) =
        NIFS::prove(ck, &mut ro_nark_prover, &mut ro_acc_prover, td2, &f_U, &f_W)?;
    let U = nifs
        .verify(&mut ro_nark_verifier, &mut ro_acc_verifier, &S, f_U, U1)
        .unwrap();
    assert_eq!(U, _U);

    f_U = _U;
    f_W = _W;
    let res = S.is_sat_relaxed(ck, &f_U, &f_W);
    assert!(res.is_ok());
    //    let perm_res = S.is_sat_perm(&f_U, &f_W);
    //    assert!(perm_res.is_ok());
    Ok(())
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
    use super::*;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Error, Instance};

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
        ) -> Result<(), Error> {
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

    #[test]
    fn test_nifs() -> Result<(), NIFSError> {
        use halo2curves::pasta::{EqAffine, Fp};

        const K: u32 = 4;
        let mut inputs1 = Vec::new();
        let mut inputs2 = Vec::new();
        for i in 1..10 {
            inputs1.push(Fp::from(i));
            inputs2.push(Fp::from(i + 1));
        }
        let circuit1 = TestCircuit::new(inputs1, Fp::from_str_vartime("2").unwrap());
        let output1 = Fp::from_str_vartime("4097").unwrap();
        let public_inputs1 = vec![output1];
        let mut td1 = TableData::<Fp>::new(K, public_inputs1);
        let _ = td1.assembly(&circuit1);

        let circuit2 = TestCircuit::new(inputs2, Fp::from_str_vartime("3").unwrap());
        let output2 = Fp::from_str_vartime("93494").unwrap();
        let public_inputs2 = vec![output2];
        let mut td2 = TableData::<Fp>::new(K, public_inputs2);
        let _ = td2.assembly(&circuit2);

        let p1 = smallest_power(td1.cs.num_advice_columns(), K);
        let p2 = smallest_power(td1.cs.num_selectors() + td1.cs.num_fixed_columns(), K);
        let ck = CommitmentKey::<EqAffine>::setup(p1.max(p2), b"zero_round_test");

        fold_instances(&ck, &td1, &td2)
    }
}

// test multiple gates without lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
mod one_round_test {
    use super::*;
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
        poly::Rotation,
    };

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
        ) -> Result<(Number<F>, Number<F>), Error> {
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
                    // println!("[0] a = {:?} b = {:?}", a.0, b.0);

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
                        // println!("[{}] a = {:?} b = {:?}", idx, a.0, b.0);
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
        ) -> Result<(), Error> {
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
        ) -> Result<(), Error> {
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

    #[test]
    fn test_nifs() -> Result<(), NIFSError> {
        use halo2curves::bn256::{Fr, G1Affine};

        const K: u32 = 4;
        let num = 16;
        // circuit 1
        let seq = get_fibo_seq(1, 1, num);
        // println!("{:?}", seq);
        let circuit1 = FiboCircuit {
            a: Fr::from(seq[0]),
            b: Fr::from(seq[1]),
            num,
        };
        let public_inputs1 = vec![Fr::from(seq[num - 1])];
        let mut td1 = TableData::<Fr>::new(K, public_inputs1);
        let _ = td1.assembly(&circuit1);

        // circuit 2
        let seq = get_fibo_seq(2, 3, num);
        let circuit2 = FiboCircuit {
            a: Fr::from(seq[0]),
            b: Fr::from(seq[1]),
            num,
        };
        let public_inputs2 = vec![Fr::from(seq[num - 1])];
        let mut td2 = TableData::<Fr>::new(K, public_inputs2);
        let _ = td2.assembly(&circuit2);

        let p1 = smallest_power(td1.cs.num_advice_columns(), K);
        let p2 = smallest_power(td1.cs.num_selectors() + td1.cs.num_fixed_columns(), K);
        let ck = CommitmentKey::<G1Affine>::setup(p1.max(p2), b"one_round_test");

        fold_instances(&ck, &td1, &td2)
    }
}
