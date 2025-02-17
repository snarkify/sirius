use std::{array, env, io, path::Path};

use bn256::G1 as C1;
use grumpkin::G1 as C2;
use metadata::LevelFilter;
use sirius::{
    commitment::CommitmentKey,
    group::{prime::PrimeCurve, Group},
    halo2curves::{bn256, grumpkin, CurveAffine},
    ivc::cyclefold,
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

/// `K` table size for primary circuit
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 21;

/// Size of commitment key
const COMMITMENT_KEY_SIZE: usize = 25;

type C1Affine = <C1 as PrimeCurve>::Affine;
type C1Scalar = <C1 as Group>::Scalar;

type C2Affine = <C2 as PrimeCurve>::Affine;

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

    let primary = sirius::gadgets::poseidon_step_circuit::TestPoseidonCircuit::default();

    let primary_commitment_key =
        get_or_create_commitment_key::<C1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get primary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<C2Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get secondary key");

    let mut pp = cyclefold::PublicParams::new(
        &primary,
        primary_commitment_key,
        secondary_commitment_key,
        PRIMARY_CIRCUIT_TABLE_SIZE as u32,
    )
    .unwrap();

    let primary_input = array::from_fn(|i| C1Scalar::from(i as u64));

    let mut ivc = cyclefold::IVC::new(&mut pp, &primary, primary_input).expect("while step=0");

    for step in 1..=1 {
        ivc = ivc
            .next(&pp, &primary)
            .unwrap_or_else(|err| panic!("while step={step}: {err:?}"));
    }

    ivc.verify(&pp).expect("while verify");
}
