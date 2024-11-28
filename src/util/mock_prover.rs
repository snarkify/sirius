use std::cell::Cell;

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::{self, MockProver as Halo2MockProver},
    halo2curves::ff::{FromUniformBytes, PrimeField},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error as PlonkError},
};
use tracing::error;

use crate::ivc::StepCircuit;

#[derive(Debug, thiserror::Error)]
pub enum VerifyFailure<const A: usize, F: PrimeField> {
    Plonk(Vec<dev::VerifyFailure>),
    OutputNotMatch { expected: [F; A], actual: [F; A] },
}

struct StepCircuitWrapper<'sc, const A: usize, F: PrimeField, SC: StepCircuit<A, F>> {
    z_i: [F; A],
    step_circuit: &'sc SC,
    last_z_out: Cell<[Value<F>; A]>,
}

impl<'sc, const A: usize, F: PrimeField, SC: StepCircuit<A, F>> StepCircuitWrapper<'sc, A, F, SC> {
    fn new(z_i: [F; A], step_circuit: &'sc SC) -> Self {
        Self {
            z_i,
            step_circuit,
            last_z_out: Cell::new([Value::unknown(); A]),
        }
    }
}

#[derive(Debug)]
struct StepCircuitConfig<const A: usize, F: PrimeField, SC: StepCircuit<A, F>> {
    input_col: Column<Advice>,
    step_circuit_config: SC::Config,
}

impl<const A: usize, F: PrimeField, SC: StepCircuit<A, F>> Clone for StepCircuitConfig<A, F, SC> {
    fn clone(&self) -> Self {
        Self {
            input_col: self.input_col,
            step_circuit_config: self.step_circuit_config.clone(),
        }
    }
}

impl<const A: usize, F: PrimeField, SC: StepCircuit<A, F>> Circuit<F>
    for StepCircuitWrapper<'_, A, F, SC>
{
    type Config = StepCircuitConfig<A, F, SC>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        todo!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Self::Config {
            input_col: meta.advice_column(),
            step_circuit_config: SC::configure(meta),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), PlonkError> {
        let z_i = layouter.assign_region(
            || "wrapper input assign",
            |mut region| {
                self.z_i
                    .iter()
                    .enumerate()
                    .map(|(i, z_ii)| {
                        region.assign_advice(
                            || "input",
                            config.input_col,
                            i,
                            || Value::known(*z_ii),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            },
        )?;

        let z_out = self
            .step_circuit
            .synthesize_step(
                config.step_circuit_config,
                &mut layouter,
                &z_i.try_into().unwrap(),
            )
            .map_err(|err| {
                error!("error while synthesize_step in MockProver: {err:?}");
                PlonkError::Synthesis
            })?;

        self.last_z_out.set(z_out.map(|c| c.value().copied()));

        Ok(())
    }
}

/// A wrapper for the Halo2 `MockProver` designed to assist in testing step circuits
///
/// This struct provides additional functionalities for initializing and verifying
/// circuits, as well as capturing the outputs of the step circuits after the proof process.
///
/// # Type Parameters
///
/// * `A`: The size of the arrays used in the step circuit.
/// * `F`: The field type, which must implement `PrimeField`.
///
/// # Examples
///
/// ```
/// use sirius::{ivc::step_circuit::trivial, util::mock_prover::MockProver};
/// use halo2_proofs::halo2curves::pasta::Fq;
///
/// let z_in = std::array::from_fn(|i| Fq::from(i as u64));
/// MockProver::run(10, &trivial::Circuit::<10, Fq>::default(), vec![], z_in)
///     .unwrap()
///     .verify(z_in)
///     .unwrap();
/// ```
pub struct MockProver<'a, const A: usize, F: Field> {
    mock_prover: Halo2MockProver<'a, F>,
    last_z_out: [Value<F>; A],
}

impl<const A: usize, F: Field> MockProver<'_, A, F> {
    /// Runs the step circuit with the provided initial input and returns
    /// a `MockProver` instance containing the resulting outputs.
    ///
    /// # Arguments
    ///
    /// * `k_table_size` - The size of the circuit's table (2^k).
    /// * `step_circuit` - A reference to the step circuit to be tested.
    /// * `instance` - The public instance values used in the circuit.
    /// * `z_i` - The initial input array for the step circuit.
    ///
    /// # Errors
    ///
    /// Returns a [`halo2_proofs::plonk::Error`] if the proof process fails.
    ///
    /// # Examples
    ///
    /// See the main struct-level example.
    pub fn run<SC: StepCircuit<A, F>>(
        k_table_size: u32,
        step_circuit: &SC,
        instance: Vec<Vec<F>>,
        z_i: [F; A],
    ) -> Result<Self, PlonkError>
    where
        F: FromUniformBytes<64> + Ord,
    {
        let circuit = StepCircuitWrapper::new(z_i, step_circuit);
        let mock_prover = Halo2MockProver::run(k_table_size, &circuit, instance)?;

        Ok(Self {
            mock_prover,
            last_z_out: circuit.last_z_out.get(),
        })
    }

    /// Verifies that the final output of the step circuit matches the expected output.
    ///
    /// # Arguments
    ///
    /// * `expected_z_out` - The expected output array to be compared with the circuit's final output.
    ///
    /// # Errors
    ///
    /// Returns a [`VerifyFailure`] if the verification fails, either due to the PLONK proof failing
    /// or the outputs not matching the expected values.
    ///
    /// # Examples
    ///
    /// See the main struct-level example.
    pub fn verify(&self, expected_z_out: [F; A]) -> Result<(), VerifyFailure<A, F>>
    where
        F: FromUniformBytes<64> + Ord,
    {
        self.mock_prover
            .verify()
            .map_err(VerifyFailure::<A, F>::Plonk)?;

        let last_z_out = self.last_z_out.map(|v| v.unwrap().unwrap_or_default());
        if expected_z_out != last_z_out {
            return Err(VerifyFailure::OutputNotMatch {
                expected: expected_z_out,
                actual: last_z_out,
            });
        }

        Ok(())
    }
}
