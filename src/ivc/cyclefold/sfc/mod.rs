use std::num::NonZeroUsize;

use crate::{
    halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        halo2curves::CurveAffine,
        plonk::{Circuit, ConstraintSystem, Error as Halo2PlonkError},
    },
    ivc::{cyclefold, StepCircuit},
    main_gate::{MainGate, MainGateConfig},
    poseidon::ROTrait,
};

mod input;
use halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits};
pub use input::Input;

const T_MAIN_GATE: usize = 5;

/// 'SCC' here is 'Step Circuit Config'
#[derive(Debug, Clone)]
pub struct Config<SCC> {
    sc: SCC,
    mg: MainGateConfig<T_MAIN_GATE>,
}

pub struct StepFoldingCircuit<
    'sc,
    const ARITY: usize,
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::ScalarExt>,
> {
    pub sc: &'sc SC,
    pub input: Input<ARITY, C::ScalarExt>,
}

impl<const ARITY: usize, C: CurveAffine, SC: StepCircuit<ARITY, C::ScalarExt>>
    StepFoldingCircuit<'_, ARITY, C, SC>
where
    C::ScalarExt: PrimeFieldBits + FromUniformBytes<64>,
{
    /// For the initial iteration, we will give the same accumulators that we take from the input
    pub fn initial_instances(&self) -> Vec<Vec<C::ScalarExt>> {
        let marker = cyclefold::ro()
            .absorb(&self.input)
            .output(NonZeroUsize::new(<C::ScalarExt as PrimeField>::NUM_BITS as usize).unwrap());

        let mut instances = self.sc.instances();
        instances.insert(0, vec![marker, marker]);
        instances
    }

    pub fn instances(&self, expected_out: C::ScalarExt) -> Vec<Vec<C::ScalarExt>> {
        let input_marker = cyclefold::ro()
            .absorb(&self.input)
            .output(NonZeroUsize::new(<C::ScalarExt as PrimeField>::NUM_BITS as usize).unwrap());

        let mut instances = self.sc.instances();
        instances.insert(0, vec![input_marker, expected_out]);
        instances
    }
}

impl<const ARITY: usize, C: CurveAffine, SC: StepCircuit<ARITY, C::ScalarExt>> Circuit<C::ScalarExt>
    for StepFoldingCircuit<'_, ARITY, C, SC>
{
    type Config = Config<SC::Config>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            sc: self.sc,
            input: self.input.get_without_witness(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<C::ScalarExt>) -> Self::Config {
        Self::Config {
            sc: SC::configure(meta),
            mg: MainGate::configure(meta),
        }
    }

    fn synthesize(
        &self,
        _config: Self::Config,
        _layouter: impl Layouter<C::ScalarExt>,
    ) -> Result<(), Halo2PlonkError> {
        todo!()
    }
}
