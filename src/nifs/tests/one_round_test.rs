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

#[traced_test]
#[test]
fn one_round_test() -> Result<(), NIFSError> {
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

    fold_instances(&ck, &S, &pair1, &pair2, G1Affine::default())
}

