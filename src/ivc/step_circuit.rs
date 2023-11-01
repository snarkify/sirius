use std::num::NonZeroUsize;

use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::ConstraintSystem,
};
use halo2curves::CurveAffine;

use crate::{
    ivc::assigned_relaxed_plonk_instance::AssignedRelaxedPlonkInstance,
    main_gate::{self, RegionCtx},
    plonk::{PlonkInstance, RelaxedPlonkInstance},
    poseidon::ROCircuitTrait,
};

use super::floor_planner::FloorPlanner;

#[derive(Debug, thiserror::Error)]
pub enum SynthesisError {
    #[error(transparent)]
    Halo2(#[from] halo2_proofs::plonk::Error),
}

/// The `StepCircuit` trait represents a step in incremental computation in
/// Incrementally Verifiable Computation (IVC).
///
/// # Overview
/// - The trait is crucial for representing a computation step within an IVC
///   framework.
/// - It provides an abstraction for handling inputs and outputs efficiently
///   at each computation step.
/// - The trait should be implemented by circuits that are intended to represent
///   a step in incremental computation.
///
/// # API
/// Design based on [`halo2_proofs::plonk::Circuit`] and
/// [`nova::traits::circuit`](https://github.com/microsoft/Nova/blob/main/src/traits/circuit.rs#L7)
///
/// # `const ARITY: usize`
/// The number of inputs or outputs of each step. `synthesize` and `output`
/// methods are expected to take as input a vector of size equal to
/// arity and output a vector of size equal to arity.
///
/// # References
/// - For a detailed understanding of IVC and the context in which a trait
///   `StepCircuit` might be used, refer to the 'Section 5' of
///   [Nova Whitepaper](https://eprint.iacr.org/2023/969.pdf).
///   This trait is representation of `F` function at 'Figure 4'
///     - `F` is a polynomial-time function that takes non-deterministic input. It is the function
///       that represents the computation being incrementally verified. In the context of IVC, each
///       step of the incremental computation applies this function FF.
/// - For `F'` please look at [`StepCircuitExt`]
pub trait StepCircuit<const ARITY: usize, F: PrimeField> {
    /// This is a configuration object that stores things like columns.
    ///
    /// TODO improve
    type Config: Clone;

    /// The floor planner used for this circuit.
    /// This is an associated type of the `Circuit` trait because its
    /// behaviour is circuit-critical.
    ///
    /// TODO improve
    ///
    /// If you don't understand what it is, just use [`super::floor_planner::SimpleStepFloorPlanner`]
    type FloopPlanner: FloorPlanner;

    /// Configure the step circuit. This method initializes necessary
    /// fixed columns and advice columns, but does not create any instance
    /// columns.
    ///
    /// This setup is crucial for the functioning of the IVC-based system.
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config;

    /// Sythesize the circuit for a computation step and return variable
    /// that corresponds to the output of the step z_{i+1}
    /// this method will be called when we synthesize the IVC_Circuit
    ///
    /// Return `z_out` result
    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_in: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError>;

    /// An auxiliary function that allows you to perform a calculation step
    /// without using ConstraintSystem.
    ///
    /// By default, performs the step with a dummy `ConstraintSystem`
    fn output(&self, z_in: &[F; ARITY]) -> [F; ARITY] {
        todo!(
            "Default impl with `Self::synthesize` wrap
            and comment about when manual impl needed by {z_in:?}"
        )
    }
}

#[derive(Debug)]
pub(crate) enum ConfigureError {
    InstanceColumnNotAllowed,
}

// TODO #32 Rename
pub(crate) struct SynthesizeStepParams<G: CurveAffine, RO: ROCircuitTrait<G::Base>>
where
    G::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    pub limb_width: NonZeroUsize,
    pub n_limbs: NonZeroUsize,
    /// A boolean indicating if this is the primary circuit
    pub is_primary_circuit: bool,
    pub ro_constant: RO::Args,
}

impl<C: CurveAffine, RO: ROCircuitTrait<C::Base>> SynthesizeStepParams<C, RO>
where
    C::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    pub fn random_oracle(&self) -> RO {
        todo!()
    }
}

// TODO #32
pub(crate) struct StepInputs<'link, const ARITY: usize, C: CurveAffine, RO: ROCircuitTrait<C::Base>>
where
    C::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    public_params: &'link SynthesizeStepParams<C, RO>,
    step: C::Base,

    z_0: [AssignedCell<C::Scalar, C::Scalar>; ARITY],
    z_in: [AssignedCell<C::Scalar, C::Scalar>; ARITY],

    // TODO docs
    U: Option<RelaxedPlonkInstance<C>>,

    // TODO docs
    u: Option<PlonkInstance<C>>,

    // TODO docs
    T_commitment: Option<Vec<C::Scalar>>,
}

// TODO #35 Change to real `T` and move it to IVC module level
const MAIN_GATE_CONFIG_SIZE: usize = 5;

type MainGateConfig = main_gate::MainGateConfig<MAIN_GATE_CONFIG_SIZE>;

pub struct StepConfig<const ARITY: usize, C: CurveAffine, SP: StepCircuit<ARITY, C::Scalar>> {
    step_config: SP::Config,
    // NOTE: check `T` size
    main_gate_config: MainGateConfig,
}

/// Trait extends [`StepCircuit`] to represent the augmented function `F'` in the IVC scheme.
///
/// If [`StepCircuit`] is defined by circuit developers, this trait automatically extends
/// the custom type to add the actions needed by IVC.
///
/// TODO #32 I will add details abote actions after implementation of trait to directly link
/// methods
///
/// # References
/// - For a detailed understanding of IVC and the context in which a trait
///   [`StepCircuitExt`] might be used, refer to the 'Section 5' of
///   [Nova Whitepaper](https://eprint.iacr.org/2023/969.pdf).
///   This trait is representation of `F'` function at 'Figure 4'
///       - `F'` is an augmented version of `F` designed to produce the IVC proofs `P_i` at each step.
///         It takes additional parameters such as \( vk, Ui, ui, (i, z0, zi), \omega_i, T \) and outputs \( x \).
///
/// - For `F'` please look at [`StepCircuitExt`]
pub(crate) trait StepCircuitExt<'link, const ARITY: usize, C: CurveAffine>:
    StepCircuit<ARITY, C::Scalar> + Sized
where
    <C as CurveAffine>::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    /// The crate-only expanding trait that checks that no instance columns have
    /// been created during [`StepCircuit::configure`].
    fn configure(
        cs: &mut ConstraintSystem<C::Scalar>,
        main_gate_config: MainGateConfig,
    ) -> Result<StepConfig<ARITY, C, Self>, ConfigureError> {
        let before = cs.num_instance_columns();

        let step_config = <Self as StepCircuit<ARITY, C::Scalar>>::configure(cs);

        if before == cs.num_instance_columns() {
            Ok(StepConfig {
                step_config,
                main_gate_config,
            })
        } else {
            Err(ConfigureError::InstanceColumnNotAllowed)
        }
    }

    fn synthesize<RO: ROCircuitTrait<C::Base, Config = MainGateConfig>>(
        &self,
        config: StepConfig<ARITY, C, Self>,
        layouter: &mut impl Layouter<C::Scalar>,
        input: StepInputs<ARITY, C, RO>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; ARITY], SynthesisError> {
        // Synthesize the circuit for the base case and get the new running instance
        let _U_new_base =
            self.synthesize_step_base_case(layouter, input.public_params, input.u.as_ref())?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let _U_new_non_base = self.synthesize_step_not_base_case(&config, layouter, input)?;

        todo!("#32")
    }

    fn synthesize_step_base_case<RO: ROCircuitTrait<C::Base, Config = MainGateConfig>>(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        public_params: &SynthesizeStepParams<C, RO>,
        u: Option<&PlonkInstance<C>>,
    ) -> Result<AssignedRelaxedPlonkInstance<C>, SynthesisError> {
        let u = u.cloned().unwrap_or_default();

        let Unew_base = layouter.assign_region(
            || "synthesize_step_base_case",
            move |region| {
                let mut ctx = RegionCtx::new(region, 0);

                AssignedRelaxedPlonkInstance::from_instance(
                    &mut ctx,
                    // TODO Move this to diff lvl
                    if public_params.is_primary_circuit {
                        PlonkInstance::default()
                    } else {
                        u.clone()
                    },
                    public_params.limb_width,
                    public_params.n_limbs,
                )
            },
        )?;

        Ok(Unew_base)
    }

    fn synthesize_step_not_base_case<RO: ROCircuitTrait<C::Base, Config = MainGateConfig>>(
        &self,
        config: &StepConfig<ARITY, C, Self>,
        layouter: &mut impl Layouter<C::Scalar>,
        input: StepInputs<ARITY, C, RO>,
    ) -> Result<AssignedRelaxedPlonkInstance<C>, SynthesisError> {
        // TODO Check hash of params

        let U = input.U.unwrap_or_default();

        let _Unew_base: AssignedRelaxedPlonkInstance<C> = layouter.assign_region(
            || "synthesize_step_non_base_case",
            move |region| {
                let mut ctx = RegionCtx::new(region, 0);

                let _U = AssignedRelaxedPlonkInstance::new(
                    &mut ctx,
                    // TODO Move this to diff lvl
                    U.clone(),
                    input.public_params.limb_width,
                    input.public_params.n_limbs,
                )?;

                let _ro_circuit = RO::new(
                    config.main_gate_config.clone(),
                    input.public_params.ro_constant.clone(),
                );

                todo!()
            },
        )?;

        todo!("#32")
    }
}

// auto-impl for all `StepCircuit` trait `StepCircuitExt`
impl<'link, const ARITY: usize, C: CurveAffine, SP: StepCircuit<ARITY, C::Scalar>>
    StepCircuitExt<'link, ARITY, C> for SP
where
    <C as CurveAffine>::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
}

pub mod trivial {
    use std::marker::PhantomData;

    use ff::PrimeField;
    use halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::ConstraintSystem,
    };

    use crate::ivc::SimpleFloorPlanner;

    use super::{StepCircuit, SynthesisError};

    /// A trivial step circuit that simply returns the input
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct Circuit<const ARITY: usize, F: PrimeField> {
        _p: PhantomData<F>,
    }

    impl<const ARITY: usize, F> StepCircuit<ARITY, F> for Circuit<ARITY, F>
    where
        F: PrimeField,
    {
        /// This is a configuration object that stores things like columns.
        ///
        /// TODO improve
        type Config = ();

        /// The floor planner used for this circuit.
        /// This is an associated type of the `Circuit` trait because its
        /// behaviour is circuit-critical.
        ///
        /// TODO improve
        ///
        /// If you don't understand what it is, just use [`super::floor_planner::SimpleStepFloorPlanner`]
        type FloopPlanner = SimpleFloorPlanner;

        /// Configure the step circuit. This method initializes necessary
        /// fixed columns and advice columns, but does not create any instance
        /// columns.
        ///
        /// This setup is crucial for the functioning of the IVC-based system.
        fn configure(_cs: &mut ConstraintSystem<F>) -> Self::Config {}

        /// Sythesize the circuit for a computation step and return variable
        /// that corresponds to the output of the step z_{i+1}
        /// this method will be called when we synthesize the IVC_Circuit
        ///
        /// Return `z_out` result
        fn synthesize_step(
            &self,
            _config: Self::Config,
            _layouter: &mut impl Layouter<F>,
            z_in: &[AssignedCell<F, F>; ARITY],
        ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError> {
            Ok(z_in.clone())
        }
    }
}
