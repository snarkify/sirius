use std::{marker::PhantomData, num::NonZeroUsize};

use itertools::Itertools;
use tracing::{error, info, info_span, instrument};

use crate::{
    halo2_proofs::{
        arithmetic::Field,
        circuit::{Layouter, SimpleFloorPlanner},
        halo2curves::CurveAffine,
        plonk::{Circuit, Column, ConstraintSystem, Error as Halo2PlonkError, Instance},
    },
    ivc::{
        cyclefold::{self, ro_chip},
        protogalaxy::{
            self,
            verify_chip::{self, VerifyResult},
        },
        StepCircuit,
    },
    main_gate::{MainGate, MainGateConfig, RegionCtx},
    nifs,
    poseidon::{ROCircuitTrait, ROTrait},
};

mod input;
pub use input::{Input, InputBuilder};

pub mod sangria_adapter;

use crate::halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits};

use super::support_circuit;

const MAIN_GATE_T: usize = 5;

/// 'SCC' here is 'Step Circuit Config'
#[derive(Debug, Clone)]
pub struct Config<SCC> {
    consistency_marker: Column<Instance>,
    sc: SCC,
    mg: MainGateConfig<MAIN_GATE_T>,
}

#[derive(Debug)]
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
    > Clone for StepFoldingCircuit<'_, ARITY, CMain, CSup, SC>
{
    fn clone(&self) -> Self {
        let Self { sc, input, _p } = self;

        Self {
            sc,
            input: input.clone(),
            _p: PhantomData,
        }
    }
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
        let mut self_ = self.input.clone();
        assert_eq!(
            self_.step, 0,
            "this method can only be called for step == 0"
        );

        self_.step = 1;
        let out_marker = cyclefold::ro().absorb(&self_).output(
            NonZeroUsize::new(<CMain::ScalarExt as PrimeField>::NUM_BITS as usize).unwrap(),
        );

        let mut instances = self.sc.instances();
        instances.insert(0, vec![out_marker]);
        instances
    }

    pub fn instances(
        &self,
        self_acc: &nifs::protogalaxy::AccumulatorInstance<CMain>,
        paired_acc: &nifs::sangria::RelaxedPlonkInstance<CSup, { support_circuit::INSTANCES_LEN }>,
        z_out: &[CMain::ScalarExt; ARITY],
    ) -> Vec<Vec<CMain::ScalarExt>> {
        let mut self_ = self.input.clone();

        self_.step += 1;
        self_.self_trace.input_accumulator = input::ProtoGalaxyAccumulatorInstance::new(self_acc);
        self_.paired_trace.input_accumulator = input::SangriaAccumulatorInstance::new(paired_acc);
        self_.z_i = *z_out;

        let out_marker = cyclefold::ro().absorb(&self_).output(
            NonZeroUsize::new(<CMain::ScalarExt as PrimeField>::NUM_BITS as usize).unwrap(),
        );

        let mut instances = self.sc.instances();
        instances.insert(0, vec![out_marker]);
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

    #[instrument(skip_all)]
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<CMain::ScalarExt>,
    ) -> Result<(), Halo2PlonkError> {
        info!("start");

        let input = layouter.assign_region(
            || "sfc input",
            |region| {
                let _span = info_span!("input").entered();

                let mut region = RegionCtx::new(region, 0);

                input::assigned::Input::assign_advice_from(&mut region, &self.input, &config.mg)?
                    .consistency_check(&mut region, &config.mg)
            },
        )?;
        info!("sfc input done");

        let z_out = {
            let _span = info_span!("sc").entered();

            self.sc
                .synthesize_step(config.sc, &mut layouter, &input.z_i)
                .map_err(|err| {
                    error!("while synthesize_step: {err:?}");
                    Halo2PlonkError::Synthesis
                })
        }?;

        info!("step circuit synthesize done");

        let self_acc_out: input::assigned::ProtoGalaxyAccumulatorInstance<CMain::ScalarExt> =
            layouter.assign_region(
                || "sfc protogalaxy",
                |region| {
                    let _span = info_span!("protogalaxy").entered();
                    let mut region = RegionCtx::new(region, 0);

                    let VerifyResult {
                        mut result_acc,
                        poly_L_values,
                    } = protogalaxy::verify_chip::verify(
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
                    })?;

                    input.pairing_check(
                        &mut region,
                        &config.mg,
                        &poly_L_values,
                        &mut result_acc,
                    )?;

                    Ok(result_acc)
                },
            )?;

        info!("protogalaxy done");

        let paired_acc_out: input::assigned::SangriaAccumulatorInstance<CMain::ScalarExt> =
            layouter
                .assign_region(
                    || "sfc sangria",
                    |region| {
                        let _span = info_span!("sangria").entered();
                        sangria_adapter::fold::<CMain, CSup>(
                            &mut RegionCtx::new(region, 0),
                            config.mg.clone(),
                            &input.paired_trace,
                        )
                    },
                )
                .inspect_err(|err| {
                    error!("while sfc sangria: {err:?}");
                })?;

        info!("sangria done");

        let consistency_marker_output = layouter.assign_region(
            || "sfc out consistency marker",
            |region| {
                let _span = info_span!("out consistency marker").entered();
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

        info!("out done");

        layouter.constrain_instance(
            consistency_marker_output.cell(),
            config.consistency_marker,
            0,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;
    use crate::{halo2_proofs::dev::MockProver, ivc::step_circuit::trivial, prelude::bn256};

    type CMain = bn256::C1Affine;
    type CSup = bn256::C2Affine;

    type Base = <CMain as CurveAffine>::Base;
    type Scalar = <CMain as CurveAffine>::ScalarExt;

    const ARITY: usize = 2;

    #[traced_test]
    #[test]
    fn e2e_zero_step() {
        let mut input = Input::<2, Scalar>::random(&mut rand::thread_rng());
        input.step = 0;

        let sc = trivial::Circuit::default();

        let sfc = StepFoldingCircuit::<ARITY, CMain, CSup, trivial::Circuit<ARITY, Scalar>> {
            sc: &sc,
            input,
            _p: PhantomData,
        };

        let instances = sfc.initial_instances();

        MockProver::run(17, &sfc, instances)
            .unwrap()
            .verify()
            .unwrap();
    }
}
