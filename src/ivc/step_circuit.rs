use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::ConstraintSystem,
};
use halo2curves::CurveAffine;

use crate::{plonk::RelaxedPlonkInstance, poseidon::ROTrait};

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
pub trait StepCircuit<const ARITY: usize, F: PrimeField> {
    type StepConfig: Clone;

    /// Configure the step circuit. This method initializes necessary
    /// fixed columns and advice columns, but does not create any instance
    /// columns.
    ///
    /// This setup is crucial for the functioning of the IVC-based system.
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::StepConfig;

    /// Sythesize the circuit for a computation step and return variable
    /// that corresponds to the output of the step z_{i+1}
    /// this method will be called when we synthesize the IVC_Circuit
    ///
    /// Return `z_out` result
    fn synthesize(
        &self,
        config: Self::StepConfig,
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

/// The private expanding trait that checks that no instance columns have
/// been created during [`StepCircuit::configure`].
///
/// IVC Circuit should use this method.
pub(crate) trait ConfigureWithInstanceCheck<const ARITY: usize, F: PrimeField>:
    StepCircuit<ARITY, F>
{
    fn configure_with_instance_check(
        cs: &mut ConstraintSystem<F>,
    ) -> Result<<Self as StepCircuit<ARITY, F>>::StepConfig, ConfigureError>;
}

impl<const A: usize, F: PrimeField, C: StepCircuit<A, F>> ConfigureWithInstanceCheck<A, F> for C {
    fn configure_with_instance_check(
        cs: &mut ConstraintSystem<F>,
    ) -> Result<<Self as StepCircuit<A, F>>::StepConfig, ConfigureError> {
        let before = cs.num_instance_columns();

        let config = <Self as StepCircuit<A, F>>::configure(cs);

        if before == cs.num_instance_columns() {
            Ok(config)
        } else {
            Err(ConfigureError::InstanceColumnNotAllowed)
        }
    }
}

// TODO Rename
pub(crate) struct SynthesizeStepParams<G: CurveAffine, RO: ROTrait<G>> {
    pub limb_width: usize,
    pub n_limbs: usize,
    /// A boolean indicating if this is the primary circuit
    pub is_primary_circuit: bool,
    pub ro_constant: RO::Constants,
}

pub(crate) struct StepInputs<'link, const ARITY: usize, C: CurveAffine, RO: ROTrait<C>> {
    params: &'link SynthesizeStepParams<C, RO>,
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

// TODO Add other
pub(crate) struct AssignedStepInputs<const ARITY: usize, C: CurveAffine> {
    params: AssignedCell<C::Scalar, C::Scalar>,
    step: AssignedCell<C::Scalar, C::Scalar>,
    u: AssignedCell<C::Scalar, C::Scalar>,
    z0: [AssignedCell<C::Scalar, C::Scalar>; ARITY],
    zi: [AssignedCell<C::Scalar, C::Scalar>; ARITY],
}

// TODO
/// Extends a step circuit so that it can be used inside an IVC
///
/// This trait functionality is equivalent to structure `NovaAugmentedCircuit` from nova codebase
pub(crate) trait StepCircuitExt<'link, const ARITY: usize, C: CurveAffine>:
    StepCircuit<ARITY, C::Scalar>
{
    fn synthesize_step<RO: ROTrait<C>>(
        &self,
        config: <Self as StepCircuit<ARITY, C::Scalar>>::StepConfig,
        layouter: &mut impl Layouter<C::Scalar>,
        input: StepInputs<ARITY, C, RO>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; ARITY], SynthesisError> {
        let assigned_input = self.alloc_witness(&config, layouter, input)?;

        // Synthesize the circuit for the base case and get the new running instance
        let _U_new_base = self.synthesize_step_base_case(layouter, &assigned_input.u)?;

        // Synthesize the circuit for the non-base case and get the new running
        // instance along with a boolean indicating if all checks have passed
        let _U_non_base = self.synthesize_step_not_base_case(&config, layouter, assigned_input)?;

        todo!()
    }

    fn alloc_witness<RO: ROTrait<C>>(
        &self,
        _config: &<Self as StepCircuit<ARITY, C::Scalar>>::StepConfig,
        _layouter: &mut impl Layouter<C::Scalar>,
        _input: StepInputs<ARITY, C, RO>,
    ) -> Result<AssignedStepInputs<ARITY, C>, SynthesisError> {
        todo!()
    }

    fn synthesize_step_base_case(
        &self,
        _layouter: &mut impl Layouter<C::Scalar>,
        _u: &AssignedCell<C::Scalar, C::Scalar>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; ARITY], SynthesisError> {
        todo!()
    }

    fn synthesize_step_not_base_case(
        &self,
        _config: &<Self as StepCircuit<ARITY, C::Scalar>>::StepConfig,
        _layouter: &mut impl Layouter<C::Scalar>,
        _assigned_input: AssignedStepInputs<ARITY, C>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; ARITY], SynthesisError> {
        todo!()
    }
}

// auto-impl for all `StepCircuit` trait `StepCircuitExt`
impl<'link, const ARITY: usize, C: CurveAffine, SP: StepCircuit<ARITY, C::Scalar>>
    StepCircuitExt<'link, ARITY, C> for SP
{
}
