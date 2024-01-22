use std::io;

use ff::{Field, FromUniformBytes, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2_proofs::circuit::{floor_planner::single_pass::SingleChipLayouter, Layouter};
use halo2curves::CurveAffine;
use serde::Serialize;

use crate::{
    ivc::{
        public_params::PublicParams,
        step_circuit::{StepCircuitExt, StepInputs, StepSynthesisResult},
    },
    main_gate::{AdviceCyclicAssignor, AssignedValue, MainGateConfig, RegionCtx},
    plonk::{PlonkInstance, PlonkTrace, PlonkWitness, RelaxedPlonkTrace, RelaxedPlonkWitness},
    poseidon::ROPair,
};

pub use super::{
    floor_planner::{FloorPlanner, SimpleFloorPlanner},
    step_circuit::{self, StepCircuit, SynthesisError},
};

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::Base>,
{
    step_circuit: SC,
    relaxed_trace: RelaxedPlonkTrace<C>,
    z_0: [AssignedValue<C::Base>; ARITY],
    z_i: [AssignedValue<C::Base>; ARITY],
}

// TODO #31 docs
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    StepConfigure(#[from] step_circuit::ConfigureError),
    #[error(transparent)]
    Plonk(#[from] halo2_proofs::plonk::Error),
    #[error(transparent)]
    Step(#[from] step_circuit::SynthesisError),
    #[error("TODO")]
    WhileHash(io::Error),
}

// TODO #31 docs
#[allow(clippy::upper_case_acronyms)]
/// RecursiveSNARK from Nova codebase
pub struct IVC<const A1: usize, const A2: usize, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC1: StepCircuit<A1, C1::Base>,
    SC2: StepCircuit<A2, C2::Base>,
{
    primary: StepCircuitContext<A1, C1, SC1>,
    secondary: StepCircuitContext<A2, C2, SC2>,

    primary_trace: PlonkTrace<C2>,

    step: usize,
}

impl<const A1: usize, const A2: usize, C1, C2, SC1, SC2> IVC<A1, A2, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
    C1::ScalarExt: Serialize,
    C2::ScalarExt: Serialize,
    SC1: StepCircuit<A1, C1::Base>,
    SC2: StepCircuit<A2, C2::Base>,
    C1::Base: PrimeFieldBits + FromUniformBytes<64>,
    C2::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    pub fn new<const T: usize, RP1, RP2>(
        pp: &mut PublicParams<C1, C2, RP1, RP2>,
        primary: SC1,
        z0_primary: [C1::Base; A1],
        _secondary: SC2,
        _z0_secondary: [C2::Base; A2],
    ) -> Result<Self, Error>
    where
        RP1: ROPair<C1::Base, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Base, Config = MainGateConfig<T>>,
    {
        let primary_pp_digest = pp.digest()?;
        let _secondary_pp_digest: C2 = pp.digest()?;
        let plonk_trace = PlonkTrace {
            u: PlonkInstance::default(), // FIXME
            w: PlonkWitness {
                W: vec![], // FIXME
            },
        };

        let primary_relaxed_trace = RelaxedPlonkTrace::<C1> {
            U: PlonkInstance::default().to_relax(),            // FIXME
            W: RelaxedPlonkWitness::new(pp.primary.td.k, &[]), // FIXME
        };

        let primary_config = <SC1 as StepCircuitExt<'_, A1, C1>>::configure(&mut pp.primary.td.cs)?;

        let primary = {
            let mut layouter =
                SingleChipLayouter::<'_, C1::Base, _>::new(&mut pp.primary.td, vec![])?;

            let primary_assigned_z0: [_; A1] = layouter.assign_region(
                || "assigned_z0_primary",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);
                    let mut advice_columns_assigner =
                        primary_config.main_gate_config.advice_cycle_assigner();
                    z0_primary
                        .iter()
                        .map(|z_0i| {
                            advice_columns_assigner.assign_next_advice(&mut ctx, || "r", *z_0i)
                        })
                        .collect::<Result<Vec<_>, _>>()
                        .map(|inp| inp.try_into().unwrap())
                },
            )?;

            let StepSynthesisResult {
                z_output: primary_assigned_z_output,
                output_hash: _primary_output_hash,
                X1: _primary_X1,
            } = primary.synthesize(
                primary_config,
                &mut layouter,
                StepInputs {
                    step_public_params: &pp.primary.params,
                    public_params_hash: primary_pp_digest,
                    step: C1::Base::ZERO,
                    z_0: primary_assigned_z0.clone(),
                    z_i: primary_assigned_z0.clone(),
                    U: primary_relaxed_trace.U.clone(),
                    u: PlonkInstance::default(), // FIXME
                    cross_term_commits: vec![],
                },
            )?;

            StepCircuitContext {
                step_circuit: primary,
                relaxed_trace: primary_relaxed_trace,
                z_0: primary_assigned_z0,
                z_i: primary_assigned_z_output,
            }
        };

        //let S = pp.primary.td.plonk_structure::<C1>(&pp.primary.ck);
        //pp.primary
        //    .td
        //    .run_sps_protocol(pp.primary.ck, ro_nark, S.num_challenges);

        #[allow(unreachable_code)]
        Ok(Self {
            primary,
            step: 1,
            primary_trace: plonk_trace,
            secondary: todo!("Logic at `RecursiveSNARK::new`"),
        })
    }

    pub fn prove_step<RO1, RO2>(
        &mut self,
        _pp: &PublicParams<C1, C2, RO1, RO2>,
        _z0_primary: [C1::Scalar; A1],
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<(), Error>
    where
        RO1: ROPair<C1::Base>,
        RO2: ROPair<C2::Base>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::prove_step`")
    }

    pub fn verify<RO1, RO2>(
        &mut self,
        _pp: &PublicParams<C1, C2, RO1, RO2>,
        _steps_count: usize,
        _z0_primary: [C1::Scalar; A1],
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<(), Error>
    where
        RO1: ROPair<C1::Base>,
        RO2: ROPair<C2::Base>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::verify`")
    }
}
