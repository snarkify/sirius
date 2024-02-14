use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::ConstraintSystem,
};

use super::{floor_planner::FloorPlanner, fold_relaxed_plonk_instance_chip};

#[derive(Debug, thiserror::Error)]
pub enum SynthesisError {
    #[error(transparent)]
    Halo2(#[from] halo2_proofs::plonk::Error),
    #[error(transparent)]
    FoldError(#[from] fold_relaxed_plonk_instance_chip::Error),
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
    type FloorPlanner: FloorPlanner;

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
        z_i: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError>;

    /// An auxiliary function that allows you to perform a calculation step
    /// without using ConstraintSystem.
    ///
    /// By default, performs the step with a dummy `ConstraintSystem`
    fn process_step(&self, z_i: &[F; ARITY]) -> [F; ARITY];
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
        type FloorPlanner = SimpleFloorPlanner;

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
            z_i: &[AssignedCell<F, F>; ARITY],
        ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError> {
            Ok(z_i.clone())
        }

        fn process_step(&self, z_i: &[F; ARITY]) -> [F; ARITY] {
            *z_i
        }
    }
}
