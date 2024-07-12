use bn256::G1 as C1;
use clap::Parser;
use sirius::{self, group::prime::PrimeCurve, halo2curves::bn256};
use tracing::metadata::LevelFilter;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

use crate::merkle::{C1Scalar, MerkleTreeUpdateCircuit};

#[allow(dead_code)]
mod merkle;

type C1Affine = <C1 as PrimeCurve>::Affine;

/// Approximately manually calculated number of lines needed for merkle-tree-circuit
/// Used to find the minimum required `k_table_size`
const ROWS: usize = 20838;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(long, default_value_t = 1)]
    repeat_count: usize,
}

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    let args = Args::parse();

    tracing_subscriber::fmt()
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        )
        .json()
        .init();

    let k_table_size = (ROWS * args.repeat_count).next_power_of_two().ilog2();

    let circuit = MerkleTreeUpdateCircuit::<C1Scalar>::new_with_random_updates(
        &mut rand::thread_rng(),
        args.repeat_count,
        1,
    );

    sirius::create_and_verify_proof!(IPA, k_table_size, circuit, &[], C1Affine);
}
