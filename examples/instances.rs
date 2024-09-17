/// This example is the debugging code for #319
///
/// When this task is closed, it should be an example of using public input in a step-circuit
use std::{array, num::NonZeroUsize};

use halo2_proofs::plonk::{Column, Instance};
use sirius::{
    ivc::{
        step_circuit::{trivial, AssignedCell, ConstraintSystem, Layouter},
        SynthesisError,
    },
    prelude::{
        bn256::{new_default_pp, C1Affine, C1Scalar, C2Affine, C2Scalar},
        CommitmentKey, PrimeField, StepCircuit, IVC,
    },
};

/// Number of folding steps
const FOLD_STEP_COUNT: usize = 5;

/// Arity : Input/output size per fold-step for primary step-circuit
const A1: usize = 5;

/// Arity : Input/output size per fold-step for secondary step-circuit
/// For tivial case it can be any number
const A2: usize = 1;

/// Table size for Primary Circuit
///
/// Requires at least 17, for service purposes, but if the primary requires more, increase the
/// constant
const SECONDARY_CIRCUIT_TABLE_SIZE: usize = 17;

/// Key size for Primary Circuit
const PRIMARY_COMMITMENT_KEY_SIZE: usize = 21;

/// Table size for Primary Circuit
///
/// Requires at least 17, for service purposes, but if the primary requires more, increase the
/// constant
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 17;

/// Key size for Primary Circuit
const SECONDARY_COMMITMENT_KEY_SIZE: usize = 21;

#[derive(Debug, Clone)]
struct InstancesConfig<const N: usize> {
    #[allow(dead_code)]
    instances: [Column<Instance>; N],
}
struct InstancesCircuit<const N: usize> {}

impl<const N: usize, const A: usize, F: PrimeField> StepCircuit<A, F> for InstancesCircuit<N> {
    type Config = InstancesConfig<N>;

    fn instances(&self) -> Vec<Vec<F>> {
        vec![vec![F::ONE]; N]
    }

    /// Configure the step circuit. This method initializes necessary
    /// fixed columns and advice columns
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        InstancesConfig {
            instances: array::from_fn(|_| {
                let c = cs.instance_column();
                cs.enable_equality(c);
                c
            }),
        }
    }

    /// Sythesize the circuit for a computation step and return variable
    /// that corresponds to the output of the step z_{i+1}
    /// this method will be called when we synthesize the IVC_Circuit
    ///
    /// Return `z_out` result
    fn synthesize_step(
        &self,
        _config: Self::Config,
        _layouter: &mut impl Layouter<F>,
        z_i: &[AssignedCell<F, F>; A],
    ) -> Result<[AssignedCell<F, F>; A], SynthesisError> {
        Ok(z_i.clone())
    }
}

fn main() {
    let sc1 = InstancesCircuit::<1> {};
    let sc2 = trivial::Circuit::<A2, C2Scalar>::default();

    let primary_commitment_key =
        CommitmentKey::<C1Affine>::setup(PRIMARY_COMMITMENT_KEY_SIZE, b"bn256");

    let secondary_commitment_key =
        CommitmentKey::<C2Affine>::setup(SECONDARY_COMMITMENT_KEY_SIZE, b"grumpkin");

    let pp = new_default_pp::<A1, _, A2, _>(
        SECONDARY_CIRCUIT_TABLE_SIZE as u32,
        &primary_commitment_key,
        &sc1,
        PRIMARY_CIRCUIT_TABLE_SIZE as u32,
        &secondary_commitment_key,
        &sc2,
    );

    IVC::fold_with_debug_mode(
        &pp,
        &sc1,
        array::from_fn(|i| C1Scalar::from(i as u64)),
        &sc2,
        array::from_fn(|i| C2Scalar::from(i as u64)),
        NonZeroUsize::new(FOLD_STEP_COUNT).unwrap(),
    )
    .unwrap();
}
