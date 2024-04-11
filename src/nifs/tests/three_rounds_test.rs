use super::*;
use halo2_proofs::circuit::Chip;
use halo2_proofs::plonk::TableColumn;
use num_bigint::BigUint as BigUintRaw;

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
    ) -> Result<(Number<F>, Number<F>, Number<F>), Error> {
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
    ) -> Result<Number<F>, Error> {
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
    ) -> Result<Number<F>, Error> {
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

    fn load_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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

#[test]
fn test_nifs() -> Result<(), NIFSError> {
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
    fold_instances(&ck, &S, &pair1, &pair2, G1Affine::default())
}

