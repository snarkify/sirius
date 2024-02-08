use std::io;
use core::marker::PhantomData;

use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use halo2_proofs::circuit::floor_planner::single_pass::SingleChipLayouter;
use halo2curves::CurveAffine;
use log::*;
use serde::Serialize;

use crate::{
    ivc::{
        public_params::{self, PublicParams},
        step_circuit::StepInputs,
    },
    main_gate::MainGateConfig,
    nifs,
    plonk::{PlonkInstance, RelaxedPlonkTrace},
    poseidon::{random_oracle::ROTrait, ROPair},
    sps,
};

pub use super::{
    floor_planner::{FloorPlanner, SimpleFloorPlanner},
    step_circuit::{self, StepCircuit, SynthesisError},
};

// TODO #31 docs
struct StepCircuitContext<const ARITY: usize, C>
where
    C: CurveAffine,
{
    pub relaxed_trace: RelaxedPlonkTrace<C>,
    pub z_0: [C::Scalar; ARITY],
    pub z_next: [C::Scalar; ARITY],
}

// TODO #31 docs
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Plonk(#[from] halo2_proofs::plonk::Error),
    #[error(transparent)]
    Step(#[from] step_circuit::SynthesisError),
    #[error("While calculate hash of pp: {0:?}")]
    WhileHash(io::Error),
    #[error("While run sps procotol: {0:?}")]
    Sps(#[from] sps::Error),
    #[error("Can't eval plonk structure, Primary - {is_primary}")]
    MissedPlonkStructure { is_primary: bool },
    #[error("While nifs: {0:?}")]
    NIFS(#[from] nifs::Error),
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
    primary: StepCircuitContext<A1, C1>,
    secondary: StepCircuitContext<A2, C2>,

    step: usize,
    _p: PhantomData<(SC1, SC2)>,
}

impl<const A1: usize, const A2: usize, C1, C2, SC1, SC2> IVC<A1, A2, C1, C2, SC1, SC2>
where
    C1: CurveAffine<Base = <C2 as PrimeCurveAffine>::Scalar> + Serialize,
    C2: CurveAffine<Base = <C1 as PrimeCurveAffine>::Scalar> + Serialize,
    C1::ScalarExt: Serialize,
    C2::ScalarExt: Serialize,
    SC1: StepCircuit<A1, C1::Scalar>,
    SC2: StepCircuit<A2, C2::Scalar>,
    C1::Base: PrimeFieldBits + FromUniformBytes<64>,
    C2::Base: PrimeFieldBits + FromUniformBytes<64>,
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
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        primary: SC1,
        z0_primary: [C1::Scalar; A1],
        secondary: SC2,
        z0_secondary: [C2::Scalar; A2],
    ) -> Result<Self, Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        // TODO #31
        info!("start ivc base case");
        let step = 0;

        let (primary_config, mut primary_td) =
            pp.primary.prepare_td(&[C1::Scalar::ZERO, C1::Scalar::ZERO]);
        debug!("primary step circuit configured");

        let (secondary_config, mut secondary_td) = pp
            .secondary
            .prepare_td(&[C2::Scalar::ZERO, C2::Scalar::ZERO]);
        debug!("secondary step circuit configured");

        let secondary_ps = secondary_td
            .plonk_structure()
            .ok_or(Error::MissedPlonkStructure { is_primary: false })?;
        let primary_cross_term_commits_len =
            secondary_ps.get_degree_for_folding().saturating_sub(1);

        let primary_ps = primary_td
            .plonk_structure()
            .ok_or(Error::MissedPlonkStructure { is_primary: true })?;
        let secondary_cross_term_commits_len =
            primary_ps.get_degree_for_folding().saturating_sub(1);

        let primary_public_params_hash = public_params::calc_digest::<C1, C2, C2, RP1, RP2>(
            pp.primary.params(),
            &primary_ps,
            pp.secondary.params(),
            &secondary_ps,
        )
        .map_err(Error::WhileHash)?;
        let secondary_public_params_hash = public_params::calc_digest::<C1, C2, C1, RP1, RP2>(
            pp.primary.params(),
            &primary_ps,
            pp.secondary.params(),
            &secondary_ps,
        )
        .map_err(Error::WhileHash)?;

        debug!("cross term commits len: primary={primary_cross_term_commits_len}, secondary={secondary_cross_term_commits_len}");

        let (primary_ctx, primary_plonk_instance) = {
            debug!("start primary synthesize");
            let StepSynthesisResult {
                z_output: primary_assigned_z_output,
                // Not used in zero step, only in verify-step, when folding is over
                new_X1: primary_new_X1,
                // Not used in zero step, only in verify-step, when folding is over
                new_X0: primary_new_X0,
            } = primary.synthesize(
                primary_config,
                &mut SingleChipLayouter::<'_, C1::Scalar, _>::new(&mut primary_td, vec![])?,
                step_circuit::StepInputs {
                    step_public_params: pp.primary.params(),
                    public_params_hash: primary_public_params_hash,
                    step: C1::Scalar::from_u128(step),
                    z_0: z0_primary,
                    z_i: z0_primary,
                    // Can be any
                    U: PlonkInstance::default().to_relax(),
                    // Can be any
                    u: PlonkInstance::default(),
                    cross_term_commits: vec![C2::identity(); primary_cross_term_commits_len],
                },
            )?;

            primary_td.instance = vec![
                *primary_new_X0.value().unwrap().unwrap(),
                *primary_new_X1.value().unwrap().unwrap(),
            ];

            debug!("start primary td postpone");
            primary_td.batch_invert_assigned();
            debug!("primary synthesized, start sps");

            let (primary_plonk_instance, primary_plonk_witness) = primary_td.run_sps_protocol(
                pp.primary.ck(),
                &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant.clone()),
                primary_td.plonk_structure().unwrap().num_challenges,
            )?;

            (
                StepCircuitContext::<A1, C1, SC1> {
                    step_circuit: primary,
                    relaxed_trace: RelaxedPlonkTrace {
                        U: primary_plonk_instance.to_relax(),
                        W: primary_plonk_witness.to_relax(pp.primary.td_k() as usize),
                    },
                    z_0: z0_primary,
                    z_next: primary_assigned_z_output
                        .map(|cell| cell.value().unwrap().copied().unwrap()),
                },
                primary_plonk_instance,
            )
        };
        debug!("primary ctx ready");

        let (secondary_ctx, secondary_prev_td) = {
            debug!("start secondary synthesize");
            let StepSynthesisResult {
                z_output: secondary_assigned_z_output,
                // Not used in zero step, only in verify-step, when folding is over
                new_X1: secondary_new_X1,
                // Not used in zero step, only in verify-step, when folding is over
                new_X0: secondary_new_X0,
            } = secondary.synthesize(
                secondary_config,
                &SingleChipLayouter::<'_, C2::Scalar, _>::new(&mut secondary_td, vec![])?,
                StepInputs {
                    step_public_params: pp.secondary.params(),
                    public_params_hash: secondary_public_params_hash,
                    step: C2::Scalar::from_u128(step),
                    z_0: z0_secondary,
                    z_i: z0_secondary,
                    // Can be any
                    U: primary_plonk_instance.to_relax(),
                    u: primary_plonk_instance.clone(),
                    cross_term_commits: vec![C1::identity(); secondary_cross_term_commits_len],
                },
            )?;

            secondary_td.instance = vec![
                *secondary_new_X0.value().unwrap().unwrap(),
                *secondary_new_X1.value().unwrap().unwrap(),
            ];

            debug!("start secondary td postpone");
            secondary_td.batch_invert_assigned();
            debug!("secondary synthesized");

            let (secondary_plonk_instance, secondary_plonk_witness) = secondary_td
                .run_sps_protocol(
                    pp.secondary.ck(),
                    &mut RP1::OffCircuit::new(pp.primary.params().ro_constant.clone()),
                    secondary_td.plonk_structure().unwrap().num_challenges,
                )?;

            (
                StepCircuitContext::<A2, C2, SC2> {
                    step_circuit: secondary,
                    relaxed_trace: RelaxedPlonkTrace {
                        U: secondary_plonk_instance.to_relax(),
                        W: secondary_plonk_witness.to_relax(pp.secondary.td_k() as usize),
                    },
                    z_0: z0_secondary,
                    z_next: secondary_assigned_z_output
                        .map(|cell| cell.value().unwrap().copied().unwrap()),
                },
                secondary_td,
            )
        };
        debug!("secondary ctx ready");

        Ok(Self {
            step: 1,
            secondary_prev_td,
            primary: primary_ctx,
            secondary: secondary_ctx,
        })
    }

    pub fn fold_step<const T: usize, RP1, RP2>(
        &mut self,
        pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar, Config = MainGateConfig<T>>,
        RP2: ROPair<C2::Scalar, Config = MainGateConfig<T>>,
    {
        let step = self.step;
        debug!("start fold step: {step}");

        let (primary_config, mut primary_td) =
            pp.primary.prepare_td(&[C1::Scalar::ZERO, C1::Scalar::ZERO]);

        (self.secondary.relaxed_trace, self.primary.z_next) = {
            debug!("start off-circuit part: nifs::prove");

            let nifs::vanilla::ProveResultCtx {
                S: _,
                w: _,
                u: secondary_plonk_instance,
                U: secondary_U,
                W: secondary_W,
                nifs: secondary_nifs,
            } = nifs::vanilla::VanillaFS::prove(
                pp.secondary.ck(),
                &pp.digest().map_err(Error::WhileHash)?,
                &mut RP1::OffCircuit::new(pp.primary.params().ro_constant.clone()),
                &mut RP1::OffCircuit::new(pp.primary.params().ro_constant.clone()),
                &self.secondary_prev_td,
                &self.secondary.relaxed_trace.U,
                &self.secondary.relaxed_trace.W,
            )?;
            debug!("nifs processed");
            debug!("start on-circuit part");

            debug!("start primary synthesize");
            let StepSynthesisResult {
                z_output: primary_assigned_z_output,
                // Not used in zero step, only in verify-step, when folding is over
                new_X1: primary_new_X1,
                // Not used in zero step, only in verify-step, when folding is over
                new_X0: primary_new_X0,
            } = self.primary.step_circuit.synthesize(
                primary_config,
                &SingleChipLayouter::<'_, C1::Scalar, _>::new(&mut primary_td, vec![])?,
                step_circuit::StepInputs {
                    step_public_params: pp.primary.params(),
                    public_params_hash: pp.digest().map_err(Error::WhileHash)?,
                    step: C1::Scalar::from_u128(self.step as u128),
                    z_0: self.primary.z_0,
                    z_i: self.primary.z_next,
                    U: secondary_U.clone(),
                    u: secondary_plonk_instance,
                    cross_term_commits: secondary_nifs.cross_term_commits,
                },
            )?;

            primary_td.instance = vec![
                *primary_new_X0.value().unwrap().unwrap(),
                *primary_new_X1.value().unwrap().unwrap(),
            ];

            debug!("start primary td postpone");
            primary_td.batch_invert_assigned();
            debug!("primary synthesized, start sps");

            (
                RelaxedPlonkTrace {
                    U: secondary_U,
                    W: secondary_W,
                },
                primary_assigned_z_output.map(|cell| cell.value().unwrap().copied().unwrap()),
            )
        };

        (
            self.primary.relaxed_trace,
            self.secondary.z_next,
            self.secondary_prev_td,
        ) = {
            let (secondary_config, mut secondary_td) = pp
                .secondary
                .prepare_td(&[C2::Scalar::ZERO, C2::Scalar::ZERO]);

            let nifs::vanilla::ProveResultCtx {
                S: _,
                w: _,
                u: primary_plonk_instance,
                U: primary_U,
                W: primary_W,
                nifs: primary_nifs,
            } = nifs::vanilla::VanillaFS::prove(
                pp.primary.ck(),
                &pp.digest().map_err(Error::WhileHash)?,
                &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant.clone()),
                &mut RP2::OffCircuit::new(pp.secondary.params().ro_constant.clone()),
                &primary_td,
                &self.primary.relaxed_trace.U,
                &self.primary.relaxed_trace.W,
            )?;

            debug!("start secondary synthesize");

            let StepSynthesisResult {
                z_output: secondary_assigned_z_output,
                // Not used in zero step, only in verify-step, when folding is over
                new_X1: secondary_new_X1,
                // Not used in zero step, only in verify-step, when folding is over
                new_X0: secondary_new_X0,
            } = self.secondary.step_circuit.synthesize(
                secondary_config,
                &SingleChipLayouter::<'_, C2::Scalar, _>::new(&mut secondary_td, vec![])?,
                step_circuit::StepInputs {
                    step_public_params: pp.secondary.params(),
                    public_params_hash: pp.digest().map_err(Error::WhileHash)?,
                    step: C2::Scalar::from_u128(self.step as u128),
                    z_0: self.secondary.z_0,
                    z_i: self.secondary.z_next,
                    U: primary_U.clone(),
                    u: primary_plonk_instance,
                    cross_term_commits: primary_nifs.cross_term_commits,
                },
            )?;

            secondary_td.instance = vec![
                *secondary_new_X0.value().unwrap().unwrap(),
                *secondary_new_X1.value().unwrap().unwrap(),
            ];

            debug!("start primary td postpone");
            primary_td.batch_invert_assigned();
            debug!("primary synthesized, start sps");

            (
                RelaxedPlonkTrace {
                    U: primary_U,
                    W: primary_W,
                },
                secondary_assigned_z_output.map(|cell| cell.value().unwrap().copied().unwrap()),
                secondary_td,
            )
        };

        self.step += 1;

        Ok(())
    }

    pub fn verify<const T: usize, RP1, RP2>(
        &mut self,
        _pp: &PublicParams<'_, A1, A2, T, C1, C2, SC1, SC2, RP1, RP2>,
        _steps_count: usize,
        _z0_primary: [C1::Scalar; A1],
        _z0_secondary: [C2::Scalar; A2],
    ) -> Result<(), Error>
    where
        RP1: ROPair<C1::Scalar>,
        RP2: ROPair<C2::Scalar>,
    {
        // TODO #31
        todo!("Logic at `RecursiveSNARK::verify`")
    }
}
