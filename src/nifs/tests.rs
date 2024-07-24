use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{self, Advice, Circuit, Column, ConstraintSystem, Instance, Selector},
    poly::Rotation,
};

use crate::{ff::PrimeField, halo2curves::group::ff::FromUniformBytes};

pub(crate) mod random_linear_combination_circuit {
    use super::*;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};

    const T: usize = 3;

    #[derive(Clone, Debug)]
    pub struct TestCircuitConfig {
        pconfig: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    pub struct RandomLinearCombinationCircuit<F: PrimeField> {
        inputs: Vec<F>,
        r: F,
    }

    impl<F: PrimeField> RandomLinearCombinationCircuit<F> {
        pub fn new(inputs: Vec<F>, r: F) -> Self {
            Self { inputs, r }
        }
    }

    impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for RandomLinearCombinationCircuit<F> {
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
}

// test multiple gates without lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
pub(crate) mod fibo_circuit {
    use super::*;

    #[derive(Clone)]
    struct Number<F: PrimeField>(AssignedCell<F, F>);

    #[derive(Debug, Clone)]
    pub struct FiboConfig {
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
    pub struct FiboCircuit<F> {
        pub a: F,
        pub b: F,
        pub num: usize,
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

    pub fn get_fibo_seq(a: u64, b: u64, num: usize) -> Vec<u64> {
        let mut seq = vec![0; num];
        seq[0] = a;
        seq[1] = b;
        for i in 2..num {
            seq[i] = seq[i - 1] + seq[i - 2];
        }
        seq
    }
}

// test vector lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
pub(crate) mod fibo_circuit_with_lookup {
    use halo2_proofs::{circuit::Chip, plonk::TableColumn};
    use num_bigint::BigUint as BigUintRaw;

    use super::*;

    pub fn f_to_u64<F: PrimeField>(f: &F) -> u64 {
        BigUintRaw::from_bytes_le(f.to_repr().as_ref())
            .try_into()
            .unwrap()
    }

    #[derive(Clone, Debug)]
    struct Number<F: PrimeField>(AssignedCell<F, F>);

    #[derive(Debug, Clone)]
    pub struct FiboConfig {
        advice: [Column<Advice>; 3],
        s_add: Selector,
        s_xor: Selector,
        xor_table: [TableColumn; 3],
    }

    pub struct FiboChip<F: PrimeField> {
        pub config: FiboConfig,
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
    pub struct FiboCircuitWithLookup<F> {
        pub a: F,
        pub b: F,
        pub c: F,
        pub num: usize,
    }

    impl<F: PrimeField> Circuit<F> for FiboCircuitWithLookup<F> {
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

    pub fn get_sequence(a: u64, b: u64, c: u64, num: usize) -> Vec<u64> {
        let mut seq = vec![0; num];
        seq[0] = a;
        seq[1] = b;
        seq[2] = c;
        for i in 3..num {
            seq[i] = seq[i - 3] + (seq[i - 2] ^ seq[i - 1]);
        }
        seq
    }
}

