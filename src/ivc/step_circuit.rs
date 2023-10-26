use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::ConstraintSystem,
};
use halo2curves::CurveAffine;

use crate::{constants::NUM_CHALLENGE_BITS, plonk::RelaxedPlonkInstance, poseidon::ROTrait};

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
pub(crate) struct SynthesizeStepParams<G: CurveAffine, RO: ROTrait<G>> {
    pub limb_width: usize,
    pub n_limbs: usize,
    /// A boolean indicating if this is the primary circuit
    pub is_primary_circuit: bool,
    pub ro_constant: RO::Constants,
}

impl<C: CurveAffine, RO: ROTrait<C>> SynthesizeStepParams<C, RO> {
    pub fn random_oracle(&self) -> RO {
        RO::new(self.ro_constant.clone())
    }

    pub fn digest(&self) -> C::Scalar {
        let Self {
            limb_width,
            n_limbs,
            is_primary_circuit,
            ro_constant,
        } = &self;

        let mut ro = RO::new(ro_constant.clone());

        ro.absorb_base(C::Base::from_u128(*limb_width as u128));
        ro.absorb_base(C::Base::from_u128(*n_limbs as u128));
        ro.absorb_base(C::Base::from_u128(*is_primary_circuit as u128));

        ro.squeeze(NUM_CHALLENGE_BITS)
    }
}

// TODO #32
pub(crate) struct StepInputs<'link, const ARITY: usize, C: CurveAffine, RO: ROTrait<C>> {
    public_params: &'link SynthesizeStepParams<C, RO>,
    step: C::Base,

    z_0: [AssignedCell<C::Scalar, C::Scalar>; ARITY],
    z_in: [AssignedCell<C::Scalar, C::Scalar>; ARITY],

    // TODO docs
    U: Option<RelaxedPlonkInstance<C>>,

    // TODO docs
    u: Option<RelaxedPlonkInstance<C>>,

    // TODO docs
    T_commitment: Option<Vec<C::Scalar>>,
}

// TODO #32 Add other
pub(crate) struct AssignedStepInputs<const ARITY: usize, C: CurveAffine> {
    public_params_commit: AssignedCell<C::Scalar, C::Scalar>,
    step: AssignedCell<C::Scalar, C::Scalar>,
    u: AssignedCell<C::Scalar, C::Scalar>,
    z0: [AssignedCell<C::Scalar, C::Scalar>; ARITY],
    zi: [AssignedCell<C::Scalar, C::Scalar>; ARITY],
}

pub struct StepConfig<const ARITY: usize, C: CurveAffine, SP: StepCircuit<ARITY, C::Scalar>> {
    config: SP::Config,
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
{
    /// The crate-only expanding trait that checks that no instance columns have
    /// been created during [`StepCircuit::configure`].
    fn configure(
        cs: &mut ConstraintSystem<C::Scalar>,
    ) -> Result<StepConfig<ARITY, C, Self>, ConfigureError> {
        let before = cs.num_instance_columns();

        let config = <Self as StepCircuit<ARITY, C::Scalar>>::configure(cs);

        if before == cs.num_instance_columns() {
            Ok(StepConfig { config })
        } else {
            Err(ConfigureError::InstanceColumnNotAllowed)
        }
    }

    fn synthesize<RO: ROTrait<C>>(
        &self,
        config: <Self as StepCircuit<ARITY, C::Scalar>>::Config,
        layouter: &mut impl Layouter<C::Scalar>,
        input: StepInputs<ARITY, C, RO>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; ARITY], SynthesisError> {
        let assigned_input = self.alloc_witness(&config, layouter, input)?;

        // Synthesize the circuit for the base case and get the new running instance
        let _U_new_base = self.synthesize_step_base_case(layouter, &assigned_input.u)?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let _U_non_base = self.synthesize_step_not_base_case(&config, layouter, assigned_input)?;

        todo!("#32")
    }

    fn alloc_witness<RO: ROTrait<C>>(
        &self,
        _config: &<Self as StepCircuit<ARITY, C::Scalar>>::Config,
        _layouter: &mut impl Layouter<C::Scalar>,
        _input: StepInputs<ARITY, C, RO>,
    ) -> Result<AssignedStepInputs<ARITY, C>, SynthesisError> {
        todo!("#32")
    }

    fn synthesize_step_base_case(
        &self,
        _layouter: &mut impl Layouter<C::Scalar>,
        _u: &AssignedCell<C::Scalar, C::Scalar>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; ARITY], SynthesisError> {
        todo!("#32")
    }

    fn synthesize_step_not_base_case(
        &self,
        _config: &<Self as StepCircuit<ARITY, C::Scalar>>::Config,
        _layouter: &mut impl Layouter<C::Scalar>,
        _assigned_input: AssignedStepInputs<ARITY, C>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; ARITY], SynthesisError> {
        todo!("#32")
    }
}

// auto-impl for all `StepCircuit` trait `StepCircuitExt`
impl<'link, const ARITY: usize, C: CurveAffine, SP: StepCircuit<ARITY, C::Scalar>>
    StepCircuitExt<'link, ARITY, C> for SP
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
