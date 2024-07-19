#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

use std::{
    fmt,
    fs::{self, File},
    path::{Path, PathBuf},
};

use clap::{Parser, Subcommand};
use git2::Repository;
use tracing::info;
use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

pub mod circuit;
mod merkle_tree_gadget;

mod ipa;
mod kzg;

mod sirius_mod {
    use std::{io, num::NonZeroUsize, path::Path};

    use halo2_proofs::halo2curves::{bn256, grumpkin, CurveAffine};
    use sirius::{
        commitment::CommitmentKey,
        ff::Field,
        group::{prime::PrimeCurve, Group},
        ivc::{step_circuit::trivial, CircuitPublicParamsInput, PublicParams, IVC},
    };
    use tracing::info_span;

    use crate::{
        circuit::MerkleTreeUpdateCircuit,
        merkle_tree_gadget::{off_circuit::Tree, *},
    };

    const ARITY: usize = 1;

    const CIRCUIT_TABLE_SIZE1: usize = 17;
    const CIRCUIT_TABLE_SIZE2: usize = 17;

    const COMMITMENT_KEY_SIZE: usize = 23;

    const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };
    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };

    type C1 = bn256::G1;
    type C2 = grumpkin::G1;

    pub type C1Scalar = <C1 as Group>::Scalar;

    type C1Affine = <C1 as PrimeCurve>::Affine;
    type C2Affine = <C2 as PrimeCurve>::Affine;
    type C2Scalar = <C2 as Group>::Scalar;

    type RandomOracle = sirius::poseidon::PoseidonRO<T, RATE>;
    type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

    fn get_or_create_commitment_key<C: CurveAffine>(
        k: usize,
        label: &'static str,
        is_recreate: bool,
    ) -> io::Result<CommitmentKey<C>> {
        const FOLDER: &str = ".cache/examples";

        unsafe { CommitmentKey::load_or_setup_cache(Path::new(FOLDER), label, k, is_recreate) }
    }

    pub fn run(repeat_count: usize, is_recreate: bool) {
        let mut rng = rand::thread_rng();

        let _span = info_span!("merkle_example").entered();
        let prepare_span = info_span!("prepare").entered();

        let mut sc1 = MerkleTreeUpdateCircuit::new_with_random_updates(&mut rng, 1, repeat_count);

        let sc2 = trivial::Circuit::<ARITY, _>::default();

        let primary_spec = RandomOracleConstant::<C1Scalar>::new(10, 10);
        let secondary_spec = RandomOracleConstant::<C2Scalar>::new(10, 10);

        let primary_commitment_key = get_or_create_commitment_key::<bn256::G1Affine>(
            COMMITMENT_KEY_SIZE,
            "bn256",
            is_recreate,
        )
        .expect("Failed to get secondary key");
        let secondary_commitment_key = get_or_create_commitment_key::<grumpkin::G1Affine>(
            COMMITMENT_KEY_SIZE,
            "grumpkin",
            is_recreate,
        )
        .expect("Failed to get primary key");

        let pp = PublicParams::<
            '_,
            ARITY,
            ARITY,
            T,
            C1Affine,
            C2Affine,
            MerkleTreeUpdateCircuit<_>,
            trivial::Circuit<ARITY, _>,
            RandomOracle,
            RandomOracle,
        >::new(
            CircuitPublicParamsInput::new(
                CIRCUIT_TABLE_SIZE1 as u32,
                &primary_commitment_key,
                primary_spec.clone(),
                &sc1,
            ),
            CircuitPublicParamsInput::new(
                CIRCUIT_TABLE_SIZE2 as u32,
                &secondary_commitment_key,
                secondary_spec.clone(),
                &sc2,
            ),
            LIMB_WIDTH,
            LIMBS_COUNT_LIMIT,
        )
        .unwrap();

        prepare_span.exit();

        let mut ivc = IVC::new(
            &pp,
            &sc1,
            [*Tree::default().get_root()],
            &sc2,
            [C2Scalar::ZERO],
            false,
        )
        .unwrap();

        for _ in 0..repeat_count {
            sc1.pop_front_proof_batch();
            ivc.fold_step(&pp, &sc1, &sc2).unwrap();
        }

        ivc.verify(&pp).unwrap();
    }
}

#[derive(clap::Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    mode: Option<ProofSystem>,
    #[arg(long, default_value_t = 1, global = true)]
    repeat_count: usize,
    #[arg(long, default_value_t = false, global = true)]
    json_logs: bool,
    #[arg(long, default_value_t = false, global = true)]
    clean_cache: bool,
    /// Push all logs into file, with name builded from params
    #[arg(long, default_value_t = false, global = true)]
    file_logs: bool,
}

pub fn build_log_folder() -> PathBuf {
    const LOGS_SUBFOLDER: &str = ".logs";

    let Ok(repo) = Repository::discover(".") else {
        return Path::new(LOGS_SUBFOLDER).to_path_buf();
    };

    // Get the current branch name
    let branch_name = repo
        .head()
        .ok()
        .and_then(|head| head.shorthand().map(String::from))
        .unwrap_or_else(|| "unknown".to_string());

    let branch_log_dir = repo
        .workdir()
        .unwrap()
        .join(LOGS_SUBFOLDER)
        .join(branch_name);

    fs::create_dir_all(&branch_log_dir)
        .unwrap_or_else(|err| panic!("Failed to create log directory {branch_log_dir:?}: {err:?}"));

    branch_log_dir
}

impl Args {
    fn build_log_filename(&self) -> Option<PathBuf> {
        if !self.file_logs {
            return None;
        }

        let Args {
            mode, repeat_count, ..
        } = &self;

        Some(build_log_folder().join(match mode {
            None | Some(ProofSystem::Sirius) => {
                format!("sirius_merkle-1_trivial-1_{repeat_count}.log")
            }
            Some(ProofSystem::Halo2Kzg) => format!("halo2_kzg_merkle_{repeat_count}.log"),
            Some(ProofSystem::Halo2Ipa) => format!("halo2_ipa_merkle_{repeat_count}.log"),
        }))
    }

    fn init_logger(&self) {
        let mut builder = tracing_subscriber::fmt()
            // Adds events to track the entry and exit of the span, which are used to build
            // time-profiling
            .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
            // Changes the default level to INFO
            .with_env_filter(
                EnvFilter::builder()
                    .with_default_directive(LevelFilter::INFO.into())
                    .from_env_lossy(),
            );

        if let Some(log_filename) = self.build_log_filename() {
            let file = File::create(&log_filename).expect("Unable to create log file");

            builder = builder.with_ansi(false);

            if self.json_logs {
                builder.json().with_writer(file).init();
            } else {
                builder.with_writer(file).init();
            }
            println!("logs will be writed to: {}", log_filename.to_string_lossy());
        } else if self.json_logs {
            builder.json().init();
        } else {
            builder.init();
        }

        info!("start with args: {self:?}");
    }
}

#[derive(Default, Debug, Subcommand, Clone, Copy)]
enum ProofSystem {
    #[default]
    Sirius,
    Halo2Kzg,
    Halo2Ipa,
}

impl fmt::Display for ProofSystem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Sirius => "sirius",
                Self::Halo2Kzg => "halo2_kzg",
                Self::Halo2Ipa => "halo2_ipa",
            }
        )
    }
}

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    let args = Args::parse();
    args.init_logger();

    match args.mode.unwrap_or_default() {
        ProofSystem::Sirius => sirius_mod::run(args.repeat_count, args.clean_cache),
        ProofSystem::Halo2Ipa => ipa::run(args.repeat_count),
        ProofSystem::Halo2Kzg => kzg::run(args.repeat_count, args.clean_cache),
    }
}
