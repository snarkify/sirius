use ff::PrimeField;
use halo2_proofs::{
    circuit::AssignedCell,
    plonk::{Assignment, Column, Fixed},
};

use super::StepCircuit;

/// A floor planning strategy for a circuit.
///
/// The floor planner is chip-agnostic and applies its strategy to the step circuit it is used
/// within.
pub trait FloorPlanner {
    type Error;
    /// Given the provided `cs`, synthesize the given step circuit.
    ///
    /// `constants` is the list of fixed columns that the layouter may use to assign
    /// global constant values. These columns will all have been equality-enabled.
    ///
    /// Internally, a floor planner will perform the following operations:
    /// - Instantiate a [`Layouter`] for this floor planner.
    /// - Perform any necessary setup or measurement tasks, which may involve one or more
    ///   calls to `Circuit::default().synthesize(config, &mut layouter)`.
    /// - Call `circuit.synthesize(config, &mut layouter)` exactly once.
    fn synthesize<const ARITY: usize, F: PrimeField, CS: Assignment<F>, C: StepCircuit<ARITY, F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
        input: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], Self::Error>;
}

mod simple_floor_planner {
    use ff::PrimeField;

    use halo2_proofs::{
        circuit::AssignedCell,
        plonk::{Assignment, Column, Fixed},
    };

    use super::{
        super::{StepCircuit, SynthesisError},
        FloorPlanner,
    };

    /// A simple [`FloorPlanner`] that performs minimal optimizations.
    ///
    /// This floor planner is suitable for debugging circuits. It aims to reflect the circuit
    /// "business logic" in the circuit layout as closely as possible. It uses a single-pass
    /// layouter that does not reorder regions for optimal packing.
    #[derive(Debug)]
    pub struct SimpleFloorPlanner;

    impl FloorPlanner for SimpleFloorPlanner {
        type Error = SynthesisError;

        fn synthesize<
            const ARITY: usize,
            F: PrimeField,
            CS: Assignment<F>,
            C: StepCircuit<ARITY, F>,
        >(
            _cs: &mut CS,
            _circuit: &C,
            _config: C::Config,
            _constants: Vec<Column<Fixed>>,
            _input: &[AssignedCell<F, F>; ARITY],
        ) -> Result<[AssignedCell<F, F>; ARITY], Self::Error> {
            todo!(
                r#"
                let layouter = SingleChipLayouter::new(cs, constants)?;
                circuit.synthesize(config, &mut layouter, input)
            "#
            )
        }
    }
}
pub use simple_floor_planner::SimpleFloorPlanner;
