use tracing_test::traced_test;

use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};

use super::*;

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
                pchip.random_linear_combination(
                    &mut RegionCtx::new(region, 0),
                    self.inputs.clone(),
                    self.r,
                )
            },
        )?;
        layouter.constrain_instance(output.cell(), config.instance, 0)?;
        Ok(())
    }
}

#[traced_test]
#[test]
fn zero_round_test() -> Result<(), NIFSError> {
    const K: u32 = 3;
    let inputs1 = (1..10).map(Fr::from).collect();
    let circuit1 = TestCircuit::new(inputs1, Fr::from_u128(2));
    let output1 = Fr::from_u128(4097);
    let public_inputs1 = vec![output1];

    let inputs2 = (2..11).map(Fr::from).collect();
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
    fold_instances(&ck, &S, &pair1, &pair2, G1Affine::default())
}
