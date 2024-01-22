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
    plonk::{PlonkInstance, PlonkTrace, RelaxedPlonkTrace},
    poseidon::{ROPair, ROTrait},
    sps,
    table::TableData,
};

pub use super::{
    floor_planner::{FloorPlanner, SimpleFloorPlanner},
    step_circuit::{self, StepCircuit, SynthesisError},
};

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C, SC>
where
    C: CurveAffine,
    SC: StepCircuit<ARITY, C::Scalar>,
{
    step_circuit: SC,
    relaxed_trace: RelaxedPlonkTrace<C>,
    z_0: [AssignedValue<C::Scalar>; ARITY],
    z_i: [AssignedValue<C::Scalar>; ARITY],
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
    #[error(transparent)]
    Sps(#[from] sps::Error),
}

// TODO #31 docs
#[allow(clippy::upper_case_acronyms)]
/// RecursiveSNARK from Nova codebase
pub struct IVC<const A1: usize, const A2: usize, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar>,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar>,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
{
    primary: StepCircuitContext<A1, C1, SC1>,
    secondary: StepCircuitContext<A2, C2, SC2>,

    secondary_trace: PlonkTrace<C2>,

    step: usize,
}

impl<const A1: usize, const A2: usize, C1, C2, SC1, SC2> IVC<A1, A2, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
    C1::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    C2::Base: PrimeFieldBits + FromUniformBytes<64> + Serialize,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
{
    /// Initializes a new instance of an Incrementally Verifiable Computation (IVC) system.
    ///
    /// This method establishes the zero round (base case) of the IVC within the context.
    /// It sets up the primary and secondary step circuits, along with their initial states (z0),
    /// and configures the necessary parameters and traces for both circuits.
    ///
    /// # Type Parameters
    /// * `T` - A constant size parameter for the [`crate::main_gate::MainGateConfig`].
    /// * `RP1`, `RP2` - Types representing the random oracle pair (on-circuit & off-circuit) for
    /// the primary and secondary curves, respectively.
    ///
    /// # Algorithmic Summary
    ///
    /// 1. **Table Data Preparation**: For both primary and secondary circuits, it initializes
    ///    [`TableData`] structures with the provided Plonk configuration parameters. These
    ///    structures are essential for building the circuit layout and assembling the proof
    ///    system.
    ///
    /// 2. **Circuit Configuration**: It configures the step circuits for both primary and
    ///    secondary contexts. This involves defining the layout and constraints of the circuits
    ///    based on the `StepCircuit` trait implementations for `SC1` and `SC2`.
    ///
    /// 3. **Initial State Assignment**: The initial states (`z0_primary` and `z0_secondary`) are
    ///    assigned to the constraint system. This forms the base case for the IVC scheme, representing
    ///    the starting point of the computation.
    ///
    /// 4. **Synthesizing the Primary Step Circuit**: Constructs the primary step circuit by
    ///    applying constraints and recording output states (`z_i`), encoding the computation for
    ///    the zero round. After run The Sumcheck Protocol over Polynomial Systems (SPS Protocol) for
    ///    receive generates [`PlonkInstance`] (`u`) & [`crate::plonk::PlonkWitness`]
    ///
    /// 5. **Synthesizing the Secondary Step Circuit**: Similarly, constructs the secondary step
    ///    circuit. Notably, it passes the [`PlonkInstance`] from the primary circuit synthesis as
    ///    [`StepInputs::u`].After run The Sumcheck Protocol over Polynomial Systems (SPS Protocol) for
    ///    receive generates [`PlonkInstance`] (`u`) & [`crate::plonk::PlonkWitness`]
    ///
    /// 6. **Creating StepCircuitContext**: For both primary and secondary circuits, a
    ///    [`StepCircuitContext`] is created, encapsulating the step circuit, its relaxed trace, and
    ///    the initial and final states.
    ///
    /// 7. **Finalizing IVC Instance**: The function concludes by constructing and returning the
    ///    `IVC` instance, which holds the contexts for both circuits.
    pub fn new<const T: usize, RP1, RP2>(
        pp: &PublicParams<C1, C2, RP2, RP1>,
        primary: SC1,
        z0_primary: [C1::Scalar; A1],
        secondary: SC2,
        z0_secondary: [C2::Scalar; A2],
    ) -> Result<Self, Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let mut primary_td = TableData::new(pp.primary.k, vec![]);
        let primary_config = primary_td.prepare_assembly(|cs| {
            // Not used in zero step, only in verify-step, when folding is over
            let _X0 = cs.instance_column();
            <SC1 as StepCircuitExt<'_, A1, C2>>::configure(cs)
        })?;

        let mut secondary_td = TableData::new(pp.secondary.k, vec![]);
        let secondary_config = secondary_td.prepare_assembly(|cs| {
            // Not used in zero step, only in verify-step, when folding is over
            let _X0 = cs.instance_column();
            <SC2 as StepCircuitExt<'_, A2, C1>>::configure(cs)
        })?;

        let primary_cross_term_commits_len = secondary_td
            .plonk_structure()
            .unwrap()
            .get_degree_for_folding();

        let secondary_cross_term_commits_len = primary_td
            .plonk_structure()
            .unwrap()
            .get_degree_for_folding();

        let (primary_ctx, primary_plonk_instance) = {
            let mut layouter =
                SingleChipLayouter::<'_, C1::Scalar, _>::new(&mut primary_td, vec![])?;

            let primary_assigned_z0: [_; A1] = layouter.assign_region(
                || "assigned_z0_primary",
                |region| {
                    primary_config
                        .main_gate_config
                        .advice_cycle_assigner()
                        .assign_all_advice(
                            &mut RegionCtx::new(region, 0),
                            || "z0_primary",
                            z0_primary.iter().copied(),
                        )
                        .map(|inp| inp.try_into().unwrap())
                },
            )?;

            let StepSynthesisResult {
                z_output: primary_assigned_z_output,
                // Not used in zero step, only in verify-step, when folding is over
                output_hash: _primary_output_hash,
                // Not used in zero step, only in verify-step, when folding is over
                X1: _primary_X1,
            } = primary.synthesize(
                primary_config,
                &mut layouter,
                StepInputs {
                    step_public_params: &pp.primary.params,
                    public_params_hash: pp.digest()?,
                    step: C1::Scalar::ZERO,
                    z_0: primary_assigned_z0.clone(),
                    z_i: primary_assigned_z0.clone(),
                    // Can be any
                    U: PlonkInstance::default().to_relax(),
                    // Can be any
                    u: PlonkInstance::default(),
                    cross_term_commits: vec![C2::identity(); primary_cross_term_commits_len],
                },
            )?;

            primary_td.postpone_assembly();

            let (primary_plonk_instance, primary_plonk_witness) = primary_td.run_sps_protocol(
                &pp.secondary.ck,
                &mut RP2::OffCircuit::new(pp.secondary.params.ro_constant.clone()),
                primary_td.plonk_structure().unwrap().num_challenges,
            )?;

            (
                StepCircuitContext::<A1, C1, SC1> {
                    step_circuit: primary,
                    relaxed_trace: RelaxedPlonkTrace {
                        U: primary_plonk_instance.to_relax(),
                        W: primary_plonk_witness.to_relax(pp.primary.k as usize),
                    },
                    z_0: primary_assigned_z0,
                    z_i: primary_assigned_z_output,
                },
                primary_plonk_instance,
            )
        };

        let (secondary_ctx, secondary_trace) = {
            let mut layouter =
                SingleChipLayouter::<'_, C2::Scalar, _>::new(&mut secondary_td, vec![])?;

            let secondary_assigned_z0: [_; A2] = layouter.assign_region(
                || "assigned_z0_secondary",
                |region| {
                    secondary_config
                        .main_gate_config
                        .advice_cycle_assigner()
                        .assign_all_advice(
                            &mut RegionCtx::new(region, 0),
                            || "z0_secondary",
                            z0_secondary.iter().copied(),
                        )
                        .map(|inp| inp.try_into().unwrap())
                },
            )?;

            let StepSynthesisResult {
                z_output: secondary_assigned_z_output,
                // Not used in zero step, only in verify-step, when folding is over
                output_hash: _secondary_output_hash,
                // Not used in zero step, only in verify-step, when folding is over
                X1: _secondary_X1,
            } = secondary.synthesize(
                secondary_config,
                &mut layouter,
                StepInputs {
                    step_public_params: &pp.secondary.params,
                    public_params_hash: pp.digest()?,
                    step: C2::Scalar::ZERO,
                    z_0: secondary_assigned_z0.clone(),
                    z_i: secondary_assigned_z0.clone(),
                    U: PlonkInstance::default().to_relax(),
                    // Can be any
                    u: primary_plonk_instance.clone(),
                    cross_term_commits: vec![C1::identity(); secondary_cross_term_commits_len],
                },
            )?;

            secondary_td.postpone_assembly();

            let (secondary_plonk_instance, secondary_plonk_witness) = secondary_td
                .run_sps_protocol(
                    &pp.primary.ck,
                    &mut RP1::OffCircuit::new(pp.primary.params.ro_constant.clone()),
                    secondary_td.plonk_structure().unwrap().num_challenges,
                )?;

            (
                StepCircuitContext::<A2, C2, SC2> {
                    step_circuit: secondary,
                    relaxed_trace: RelaxedPlonkTrace {
                        U: secondary_plonk_instance.to_relax(),
                        W: secondary_plonk_witness.to_relax(pp.secondary.k as usize),
                    },
                    z_0: secondary_assigned_z0,
                    z_i: secondary_assigned_z_output,
                },
                PlonkTrace {
                    u: secondary_plonk_instance,
                    w: secondary_plonk_witness,
                },
            )
        };

        Ok(Self {
            step: 1,
            secondary_trace,
            primary: primary_ctx,
            secondary: secondary_ctx,
        })
    }

    pub fn fold_step<RO1, RO2>(
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
