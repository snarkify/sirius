/// This module represents an implementation of `StepCircuit` based on the poseidon chip
use std::{array, env, io, num::NonZeroUsize, path::Path};

use bn256::G1 as C1;
use grumpkin::G1 as C2;
use metadata::LevelFilter;
use sirius::{
    commitment::CommitmentKey,
    gadgets::poseidon_step_circuit::TestPoseidonCircuit,
    group::{prime::PrimeCurve, Group},
    halo2curves::{bn256, grumpkin, CurveAffine},
    ivc::{sangria, step_circuit},
    poseidon::{self, ROPair},
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

const ARITY: usize = 1;

/// `K` table size for primary circuit
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 17;
/// `K` table size for secondary circuit
const SECONDARY_CIRCUIT_TABLE_SIZE: usize = 17;

/// Size of commitment key
const COMMITMENT_KEY_SIZE: usize = 21;

/// Specification for the random oracle used within IVC
const MAIN_GATE_SIZE: usize = 5;
const RATE: usize = 4;

type RandomOracle = poseidon::PoseidonRO<MAIN_GATE_SIZE, RATE>;
type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

/// Inside the IVC, big-uint math is used, these parameters define width of one limb
const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
/// Inside the IVC, big-uint math is used, these parameters define maximum count of limbs
const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

type C1Affine = <C1 as PrimeCurve>::Affine;
type C1Scalar = <C1 as Group>::Scalar;

type C2Affine = <C2 as PrimeCurve>::Affine;
type C2Scalar = <C2 as Group>::Scalar;

/// Either takes the key from [`CACHE_FOLDER`] or generates a new one and puts it in it
#[instrument]
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
    let builder = tracing_subscriber::fmt()
        // Adds events to track the entry and exit of the span, which are used to build
        // time-profiling
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        // Changes the default level to INFO
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        );

    // Structured logs are needed for time-profiling, while for simple run regular logs are
    // more convenient.
    //
    // So this expr keeps track of the --json argument for turn-on json-logs
    if env::args().any(|arg| arg.eq("--json")) {
        builder.json().init();
    } else {
        builder.init();
    }

    // To osterize the total execution time of the example
    let _span = info_span!("poseidon_example").entered();

    let primary = TestPoseidonCircuit::default();
    let secondary = step_circuit::trivial::Circuit::<ARITY, _>::default();

    // Specifications for random oracle used as part of the IVC algorithm
    let primary_spec = RandomOracleConstant::<C1Scalar>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<C2Scalar>::new(10, 10);

    let primary_commitment_key =
        get_or_create_commitment_key::<C1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get primary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<C2Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get secondary key");

    let pp = sangria::PublicParams::<
        '_,
        ARITY,
        ARITY,
        MAIN_GATE_SIZE,
        C1Affine,
        C2Affine,
        TestPoseidonCircuit<_>,
        step_circuit::trivial::Circuit<ARITY, _>,
        RandomOracle,
        RandomOracle,
    >::new(
        sangria::CircuitPublicParamsInput::new(
            PRIMARY_CIRCUIT_TABLE_SIZE as u32,
            &primary_commitment_key,
            primary_spec,
            &primary,
        ),
        sangria::CircuitPublicParamsInput::new(
            SECONDARY_CIRCUIT_TABLE_SIZE as u32,
            &secondary_commitment_key,
            secondary_spec,
            &secondary,
        ),
        LIMB_WIDTH,
        LIMBS_COUNT,
    )
    .unwrap();

    let primary_input = array::from_fn(|i| C1Scalar::from(i as u64));
    let secondary_input = array::from_fn(|i| C2Scalar::from(i as u64));

    sangria::IVC::fold_with_debug_mode(
        &pp,
        &primary,
        primary_input,
        &secondary,
        secondary_input,
        NonZeroUsize::new(10).unwrap(),
    )
    .unwrap();
}
