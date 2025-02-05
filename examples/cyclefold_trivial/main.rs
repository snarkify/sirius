use std::{array, path::Path};

use sirius::{commitment::CommitmentKey, ff::Field, ivc::step_circuit::trivial};

/// Arity : Input/output size per fold-step for primary step-circuit
/// For tivial case it can be any number
const A1: usize = 5;

/// Key size for Primary Circuit
const PRIMARY_COMMITMENT_KEY_SIZE: usize = 23;

/// Table size for Primary Circuit
///
/// Requires at least 17, for service purposes, but if the primary requires more, increase the
/// constant
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 20;

/// Key size for Primary Circuit
const SECONDARY_COMMITMENT_KEY_SIZE: usize = 23;

use sirius::cyclefold_prelude::{
    bn256::{C1Affine, C1Scalar, C2Affine},
    PublicParams, IVC,
};

const FOLDER: &str = ".cache/examples";

fn main() {
    let sc = trivial::Circuit::<A1, C1Scalar>::default();

    let primary_commitment_key = unsafe {
        CommitmentKey::<C1Affine>::load_or_setup_cache(
            Path::new(FOLDER),
            "bn256",
            PRIMARY_COMMITMENT_KEY_SIZE,
        )
        .unwrap()
    };

    let secondary_commitment_key = unsafe {
        CommitmentKey::<C2Affine>::load_or_setup_cache(
            Path::new(FOLDER),
            "grumpkin",
            SECONDARY_COMMITMENT_KEY_SIZE,
        )
        .unwrap()
    };

    let mut pp = PublicParams::new(
        &sc,
        primary_commitment_key,
        secondary_commitment_key,
        PRIMARY_CIRCUIT_TABLE_SIZE as u32,
    )
    .unwrap();

    IVC::new(&mut pp, &sc, array::from_fn(|_| C1Scalar::ZERO))
        .expect("while step=0")
        .next(&pp, &sc)
        .expect("while step=1")
        .verify(&pp)
        .expect("while verify");
}
