use std::{marker::PhantomData, num::NonZeroUsize};

use itertools::Itertools;
use tracing::error;

use crate::{
    halo2_proofs::{
        arithmetic::Field,
        circuit::{Layouter, SimpleFloorPlanner},
        halo2curves::CurveAffine,
        plonk::{Circuit, Column, ConstraintSystem, Error as Halo2PlonkError, Instance},
    },
    ivc::{
        cyclefold::{self, ro_chip},
        protogalaxy::{self, verify_chip},
        StepCircuit,
    },
    main_gate::{MainGate, MainGateConfig, RegionCtx},
    poseidon::{ROCircuitTrait, ROTrait},
};

mod input;
pub use input::Input;

pub mod sangria_adapter;

use crate::halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits};

const MAIN_GATE_T: usize = 5;

/// 'SCC' here is 'Step Circuit Config'
#[derive(Debug, Clone)]
pub struct Config<SCC> {
    consistency_marker: Column<Instance>,
    sc: SCC,
    mg: MainGateConfig<MAIN_GATE_T>,
}

pub struct StepFoldingCircuit<
    'sc,
    const ARITY: usize,
    CMain: CurveAffine,
    CSup: CurveAffine<Base = CMain::ScalarExt>,
    SC: StepCircuit<ARITY, CMain::ScalarExt>,
> {
    pub sc: &'sc SC,
    pub input: Input<ARITY, CMain::ScalarExt>,
    pub _p: PhantomData<CSup>,
}

impl<
        const ARITY: usize,
        CMain: CurveAffine,
        CSup: CurveAffine<Base = CMain::ScalarExt>,
        SC: StepCircuit<ARITY, CMain::ScalarExt>,
    > StepFoldingCircuit<'_, ARITY, CMain, CSup, SC>
where
    CMain::ScalarExt: PrimeFieldBits + FromUniformBytes<64>,
{
    /// For the initial iteration, we will give the same accumulators that we take from the input
    pub fn initial_instances(&self) -> Vec<Vec<CMain::ScalarExt>> {
        let marker = cyclefold::ro().absorb(&self.input).output(
            NonZeroUsize::new(<CMain::ScalarExt as PrimeField>::NUM_BITS as usize).unwrap(),
        );

        let mut instances = self.sc.instances();
        instances.insert(0, vec![marker]);
        instances
    }

    pub fn instances(&self, expected_out: CMain::ScalarExt) -> Vec<Vec<CMain::ScalarExt>> {
        let mut instances = self.sc.instances();
        instances.insert(0, vec![expected_out]);
        instances
    }
}

impl<
        const ARITY: usize,
        CMain: CurveAffine,
        CSup: CurveAffine<Base = CMain::ScalarExt>,
        SC: StepCircuit<ARITY, CMain::ScalarExt>,
    > Circuit<CMain::ScalarExt> for StepFoldingCircuit<'_, ARITY, CMain, CSup, SC>
where
    CMain::ScalarExt: PrimeFieldBits + FromUniformBytes<64>,
{
    type Config = Config<SC::Config>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            sc: self.sc,
            input: self.input.get_without_witness(),
            _p: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<CMain::ScalarExt>) -> Self::Config {
        let consistency_marker = meta.instance_column();
        meta.enable_equality(consistency_marker);

        Self::Config {
            consistency_marker,
            sc: SC::configure(meta),
            mg: MainGate::configure(meta),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<CMain::ScalarExt>,
    ) -> Result<(), Halo2PlonkError> {
        let input = layouter.assign_region(
            || "sfc input",
            |region| {
                let mut region = RegionCtx::new(region, 0);

                input::assigned::Input::assign_advice_from(&mut region, &self.input, &config.mg)?
                    .consistency_check(&mut region, &config.mg)
            },
        )?;

        let z_out = self
            .sc
            .synthesize_step(config.sc, &mut layouter, &input.z_i)
            .map_err(|err| {
                error!("while synthesize_step: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        let self_acc_out: input::assigned::ProtoGalaxyAccumulatorInstance<CMain::ScalarExt> =
            layouter.assign_region(
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

        let paired_acc_out: input::assigned::SangriaAccumulatorInstance<CMain::ScalarExt> =
            layouter.assign_region(
                || "sfc sangria",
                |region| {
                    sangria_adapter::fold::<CMain, CSup>(
                        &mut RegionCtx::new(region, 0),
                        config.mg.clone(),
                        &input.paired_trace,
                    )
                },
            )?;

        let consistency_marker_output = layouter.assign_region(
            || "sfc out",
            |region| {
                let mut region = RegionCtx::new(region, 0);

                let mg = MainGate::new(config.mg.clone());
                let is_zero_step = mg.is_zero_term(&mut region, input.step.clone())?;

                let z_out: [_; ARITY] = input
                    .z_0
                    .iter()
                    .zip_eq(z_out.iter())
                    .map(|(z_0_i, z_out_i)| {
                        mg.conditional_select(&mut region, z_0_i, z_out_i, &is_zero_step)
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .try_into()
                    .unwrap();

                let self_trace_output =
                    input::assigned::ProtoGalaxyAccumulatorInstance::conditional_select(
                        &mut region,
                        &mg,
                        &input.self_trace.input_accumulator,
                        &self_acc_out,
                        &is_zero_step,
                    )?;

                let paired_trace_output =
                    input::assigned::SangriaAccumulatorInstance::conditional_select(
                        &mut region,
                        &mg,
                        &input.paired_trace.input_accumulator,
                        &paired_acc_out,
                        &is_zero_step,
                    )?;

                let next_step =
                    mg.add_with_const(&mut region, &input.step, CMain::ScalarExt::ONE)?;

                ro_chip(config.mg.clone())
                    .absorb_iter(input::assigned::iter_consistency_marker_wrap_values(
                        (&input.pp_digest.0, &input.pp_digest.1),
                        &self_trace_output,
                        &paired_trace_output,
                        &next_step,
                        &input.z_0,
                        &z_out,
                    ))
                    .squeeze(&mut region)
            },
        )?;

        layouter.constrain_instance(
            consistency_marker_output.cell(),
            config.consistency_marker,
            0,
        )?;

        Ok(())
    }
}
