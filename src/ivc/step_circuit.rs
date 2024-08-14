use tracing::*;

use super::fold_relaxed_plonk_instance_chip;
pub use crate::halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::ConstraintSystem,
};

use crate::{
    ff::PrimeField,
    halo2_proofs::circuit::{floor_planner::single_pass::SingleChipLayouter, Value},
    main_gate::RegionCtx,
    table::WitnessCollector,
};

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

    /// Off-circuit version of [`StepCircuit::synthesize_step`]
    ///
    /// As part of the IVC calculation, we need to know what the output of the step circuit will be
    /// before performing on-circuit calculations. This method will be called to define `z_out` and
    /// use it within the IVC algo.
    ///
    /// The default implementation includes calling step synthesis on `TableData` where table size is
    /// equal to that specified in the IVC fold call. However, if these calculations are long and resource
    /// intensive, it is possible to implement this logic off-circuit "honestly" with regular code, which may
    /// be more lightweight, but will require consistency testing.
    #[instrument(skip_all)]
    fn process_step(
        &self,
        z_i: &[F; ARITY],
        k_table_size: u32,
    ) -> Result<[F; ARITY], SynthesisError> {
        let mut cs = ConstraintSystem::default();
        let col = cs.advice_column();
        let config = Self::configure(&mut cs);

        let mut witness = WitnessCollector {
            instance: vec![F::ZERO, F::ZERO],
            advice: vec![vec![F::ZERO.into(); 1 << k_table_size as usize]; cs.num_advice_columns()],
        };
        let mut layouter =
            SingleChipLayouter::<'_, F, _>::new(&mut witness, vec![]).map_err(|err| {
                error!("while creation of layouter in `process_step`: {err:?}");
                SynthesisError::Halo2(err)
            })?;

        let assigned_z_i = layouter
            .assign_region(
                || "z_i",
                |region| {
                    let mut region = RegionCtx::new(region, 0);

                    z_i.iter()
                        .map(|value| {
                            let assigned =
                                region.assign_advice(|| "", col, Value::known(*value))?;

                            region.next();

                            Ok(assigned)
                        })
                        .collect::<Result<Vec<_>, _>>()
                },
            )
            .map_err(|err| {
                error!("while assign z input: {err:?}");
                SynthesisError::Halo2(err)
            })?;

        self.synthesize_step(config, &mut layouter, &assigned_z_i.try_into().unwrap())
            .map(|z_out| z_out.map(|cell| cell.value().unwrap().copied().unwrap()))
    }
}

pub mod trivial {
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::ConstraintSystem,
    };

    use super::{StepCircuit, SynthesisError};
    use crate::ff::PrimeField;

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
    }
}
