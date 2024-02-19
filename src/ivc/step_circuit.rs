use ff::PrimeField;
use halo2_proofs::{
    circuit::{floor_planner::single_pass::SingleChipLayouter, AssignedCell, Layouter, Value},
    plonk::{ConstraintSystem, Error, FloorPlanner},
};

use crate::{main_gate::RegionCtx, table::WitnessData};

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
    ) -> Result<[AssignedCell<F, F>; ARITY], Error>;

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
    fn process_step(&self, z_i: &[F; ARITY]) -> Result<[F; ARITY], Error> {
        let mut witness = WitnessData {
            instance: vec![],
            advice: vec![],
        };
        let mut layouter = SingleChipLayouter::<'_, F, _>::new(&mut witness, vec![])?;
        let mut cs = ConstraintSystem::default();
        let config = Self::configure(&mut cs);

        let assigned_z_i = layouter.assign_region(
            || "z_i",
            |region| {
                let mut region = RegionCtx::new(region, 0);

                z_i.iter()
                    .map(|value| {
                        let assigned = region.assign_advice(
                            || "",
                            cs.advice_column(),
                            Value::known(*value),
                        )?;

                        region.next();

                        Ok(assigned)
                    })
                    .collect::<Result<Vec<_>, _>>()
            },
        )?;

        self.synthesize_step(config, &mut layouter, &assigned_z_i.try_into().unwrap())
            .map(|z_out| z_out.map(|cell| cell.value().unwrap().copied().unwrap()))
    }
}

pub mod simple_step {
    use super::StepCircuit;
    use ff::PrimeField;
    use halo2_proofs::{
        circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Column, ConstraintSystem, Error, Expression::Constant, Selector},
        poly::Rotation,
    };

    /// A trivial step circuit that simply returns the input
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct Circuit<F: PrimeField> {
        input: F,
    }

    #[derive(Debug, Clone)]
    pub struct Config {
        col: Column<Advice>,
        selector: Selector,
    }

    impl<F> StepCircuit<1, F> for Circuit<F>
    where
        F: PrimeField,
    {
        /// This is a configuration object that stores things like columns.
        ///
        /// TODO improve
        type Config = Config;

        /// The floor planner used for this circuit.
        /// This is an associated type of the `Circuit` trait because its
        /// behaviour is circuit-critical.
        type FloorPlanner = SimpleFloorPlanner;

        /// Configure the step circuit. This method initializes necessary
        /// fixed columns and advice columns, but does not create any instance
        /// columns.
        ///
        /// This setup is crucial for the functioning of the IVC-based system.
        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let col = meta.advice_column();
            let selector = meta.selector();
            meta.enable_equality(col);
            meta.create_gate("step_circuit_gate", |meta| {
                let s = meta.query_selector(selector);
                let a1 = meta.query_advice(col, Rotation::prev());
                let a2 = meta.query_advice(col, Rotation::cur());
                vec![s * (a2 - a1 - Constant(F::from_u128(1)))]
            });
            Config { col, selector }
        }

        /// Sythesize the circuit for a computation step and return variable
        /// that corresponds to the output of the step z_{i+1}
        /// this method will be called when we synthesize the IVC_Circuit
        ///
        /// Return `z_out` result
        fn synthesize_step(
            &self,
            config: Self::Config,
            layouter: &mut impl Layouter<F>,
            z_i: &[AssignedCell<F, F>; 1],
        ) -> Result<[AssignedCell<F, F>; 1], Error> {
            let z_out = layouter.assign_region(
                || "step_circuit",
                |mut region| {
                    let z_in = z_i[0].copy_advice(|| "z_in", &mut region, config.col, 0)?;
                    let val = z_in.value().copied() + Value::known(F::from_u128(1));
                    region.assign_advice(|| "z_out", config.col, 1, || val)
                },
            )?;
            Ok([z_out])
        }
    }
}

pub mod trivial {
    use super::StepCircuit;
    use ff::PrimeField;
    use halo2_proofs::{
        circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
        plonk::{ConstraintSystem, Error},
    };
    use std::marker::PhantomData;

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
        ) -> Result<[AssignedCell<F, F>; ARITY], Error> {
            Ok(z_i.clone())
        }
    }
}
