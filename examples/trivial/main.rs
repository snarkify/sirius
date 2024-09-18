use std::{array, io, num::NonZeroUsize, path::Path};

use halo2_proofs::halo2curves::CurveAffine;
use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit::trivial, IVC},
};

/// Arity : Input/output size per fold-step for primary step-circuit
/// For tivial case it can be any number
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

use sirius::prelude::bn256::{new_default_pp, C1Affine, C1Scalar, C2Affine, C2Scalar};
use tracing::info;
use tracing_subscriber::{filter::LevelFilter, EnvFilter};

pub fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    /// Relative directory where the generated `CommitmentKey` stored
    const CACHE_FOLDER: &str = ".cache/examples";

    // Safety: Safe if you have not manually modified the generated files in [`CACHE_FOLDER`]
    unsafe { CommitmentKey::load_or_setup_cache(Path::new(CACHE_FOLDER), label, k) }
}

fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::DEBUG.into())
                .from_env_lossy(),
        )
        .init();

    info!("start");

    let sc1 = trivial::Circuit::<A1, C1Scalar>::default();
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
        NonZeroUsize::new(5).unwrap(),
    )
    .unwrap();
}
