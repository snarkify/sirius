use std::num::NonZeroUsize;

use itertools::Itertools;
use tracing::error;

use crate::{
    halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        halo2curves::CurveAffine,
        plonk::{Circuit, ConstraintSystem, Error as Halo2PlonkError},
    },
    ivc::{
        cyclefold::{self, ro_chip},
        protogalaxy::{self, verify_chip},
        StepCircuit,
    },
    main_gate::{MainGate, MainGateConfig, RegionCtx},
    poseidon::ROTrait,
};

mod input;
pub use input::Input;

use crate::halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits};

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
where
    C::ScalarExt: PrimeFieldBits + FromUniformBytes<64>,
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
        config: Self::Config,
        mut layouter: impl Layouter<C::ScalarExt>,
    ) -> Result<(), Halo2PlonkError> {
        let input = layouter.assign_region(
            || "sfc input",
            |region| {
                let mut region = RegionCtx::new(region, 0);

                input::assigned::Input::assign_advice_from(&mut region, &self.input, &config.mg)
            },
        )?;

        let z_out = self
            .sc
            .synthesize_step(config.sc, &mut layouter, &input.z_i)
            .map_err(|err| {
                error!("while synthesize_step: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        let _self_acc_out: input::assigned::ProtoGalaxyAccumulatorInstance<C::ScalarExt> = layouter
            .assign_region(
                || "sfc protogalaxy",
                |region| {
                    let mut region = RegionCtx::new(region, 0);

                    protogalaxy::verify_chip::verify(
                        &mut region,
                        config.mg.clone(),
                        ro_chip(config.mg.clone()),
                        verify_chip::AssignedVerifierParam {
                            pp_digest: input.pp_digest.clone(),
                        },
                        input.self_trace.input_accumulator.clone(),
                        &[input.self_trace.incoming.clone()],
                        input.self_trace.proof.clone(),
                    )
                    .map_err(|err| {
                        error!("while protogalaxy::verify: {err:?}");
                        Halo2PlonkError::Synthesis
                    })
                },
            )?;

        layouter.assign_region(
            || "sfc out",
            |region| {
                let mut region = RegionCtx::new(region, 0);

                let mg = MainGate::new(config.mg.clone());
                let is_zero_step = mg.is_zero_term(&mut region, input.step.clone())?;

                let _z_out: [_; ARITY] = input
                    .z_0
                    .iter()
                    .zip_eq(z_out.iter())
                    .map(|(z_0_i, z_out_i)| {
                        mg.conditional_select(&mut region, z_0_i, z_out_i, &is_zero_step)
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .try_into()
                    .unwrap();

                Ok(())
            },
        )?;

        todo!()
    }
}
