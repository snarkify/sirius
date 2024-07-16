#![allow(dead_code)]

use std::{array, env, io, num::NonZeroUsize, path::Path};

use bn256::G1 as C1;
use grumpkin::G1 as C2;
use metadata::LevelFilter;
use sirius::{
    commitment::CommitmentKey,
    group::{prime::PrimeCurve, Group},
    halo2curves::{bn256, grumpkin, CurveAffine, CurveExt},
    ivc::{step_circuit, CircuitPublicParamsInput, PublicParams, IVC},
    poseidon::{self, ROPair},
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

const ARITY: usize = BLOCK_SIZE / 2;
const BLOCK_SIZE: usize = 16;

const CIRCUIT_TABLE_SIZE1: usize = 17;
const CIRCUIT_TABLE_SIZE2: usize = 17;
const COMMITMENT_KEY_SIZE: usize = 20;
const T: usize = 5;
const RATE: usize = 4;

type RandomOracle = poseidon::PoseidonRO<T, RATE>;

type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

type C1Affine = <C1 as PrimeCurve>::Affine;
type C2Affine = <C2 as PrimeCurve>::Affine;

type C1Scalar = <C1 as Group>::Scalar;
type C2Scalar = <C2 as Group>::Scalar;

const FOLDER: &str = ".cache/examples";

#[instrument]
fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    unsafe { CommitmentKey::load_or_setup_cache(Path::new(FOLDER), label, k, false) }
}

fn main() {
    let builder = tracing_subscriber::fmt()
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        );

    if env::args().any(|arg| arg.eq("--json")) {
        builder.json().init();
    } else {
        builder.init();
    }

    let _span = info_span!("trivial_example").entered();

    // C1
    let sc1 = step_circuit::trivial::Circuit::<ARITY, _>::default();
    // C2
    let sc2 = step_circuit::trivial::Circuit::<ARITY, _>::default();

    let primary_spec = RandomOracleConstant::<<C1 as CurveExt>::ScalarExt>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<<C2 as CurveExt>::ScalarExt>::new(10, 10);

    let primary_commitment_key =
        get_or_create_commitment_key::<C1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get primary key");
    info!("Primary generated");
    let secondary_commitment_key =
        get_or_create_commitment_key::<C2Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get secondary key");
    info!("Secondary generated");

    let pp = PublicParams::<
        '_,
        ARITY,
        ARITY,
        T,
        C1Affine,
        C2Affine,
        step_circuit::trivial::Circuit<ARITY, _>,
        step_circuit::trivial::Circuit<ARITY, _>,
        RandomOracle,
        RandomOracle,
    >::new(
        CircuitPublicParamsInput::new(
            CIRCUIT_TABLE_SIZE1 as u32,
            &primary_commitment_key,
            primary_spec,
            &sc1,
        ),
        CircuitPublicParamsInput::new(
            CIRCUIT_TABLE_SIZE2 as u32,
            &secondary_commitment_key,
            secondary_spec,
            &sc2,
        ),
        LIMB_WIDTH,
        LIMBS_COUNT_LIMIT,
    )
    .unwrap();
    info!("public params: {pp:?}");

    debug!("start ivc");
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
