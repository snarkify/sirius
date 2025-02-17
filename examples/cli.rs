#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

use std::{
    fmt,
    fs::{self, File},
    num::NonZeroUsize,
    path::{Path, PathBuf},
};

use clap::{Parser, Subcommand, ValueEnum};
use git2::Repository;
use halo2_proofs::halo2curves;
use sirius::{
    ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
    gadgets::poseidon_step_circuit::TestPoseidonCircuit,
    ivc::{cyclefold, sangria, step_circuit::trivial, StepCircuit},
    poseidon::ROPair,
};
use tracing::*;
use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

#[allow(dead_code)]
mod sangria_poseidon;
use sangria_poseidon as poseidon;

#[allow(dead_code)]
mod merkle;

use merkle::{MerkleTreeUpdateCircuit, Tree};

#[derive(Parser, Debug)]
#[command(name = "sirius", version, about, long_about = None)]
pub struct Args {
    // Global options common to both modes
    #[arg(long, default_value_t = NonZeroUsize::new(32).unwrap())]
    pub limb_width: NonZeroUsize,
    #[arg(long, default_value_t = NonZeroUsize::new(10).unwrap())]
    pub limbs_count: NonZeroUsize,
    #[arg(long, default_value_t = false)]
    pub debug_mode: bool,
    #[arg(long, default_value_t = NonZeroUsize::new(1).unwrap())]
    pub fold_step_count: NonZeroUsize,
    #[arg(long, default_value_t = false)]
    pub json_logs: bool,
    /// Push all logs into file, with name built from parameters.
    #[arg(long, default_value_t = false)]
    pub file_logs: bool,

    #[command(subcommand)]
    pub mode: Mode,
}

impl Args {
    fn primary_commitment_key_size(&self) -> usize {
        match &self.mode {
            Mode::Sangria(args) => args.primary_commitment_key_size,
            Mode::Cyclefold(args) => args.primary_commitment_key_size,
        }
    }
    fn secondary_commitment_key_size(&self) -> usize {
        match &self.mode {
            Mode::Sangria(args) => args.secondary_commitment_key_size,
            Mode::Cyclefold(_) => 23,
        }
    }

    fn primary_repeat_count(&self) -> usize {
        match &self.mode {
            Mode::Sangria(args) => args.primary_repeat_count,
            Mode::Cyclefold(args) => args.primary_repeat_count,
        }
    }
    fn secondary_repeat_count(&self) -> usize {
        match &self.mode {
            Mode::Sangria(args) => args.secondary_repeat_count,
            Mode::Cyclefold(_) => 0,
        }
    }
    fn primary_circuit(&self) -> Circuits {
        match &self.mode {
            Mode::Sangria(args) => args.primary_circuit,
            Mode::Cyclefold(args) => args.primary_circuit,
        }
    }
    fn secondary_circuit(&self) -> Circuits {
        match &self.mode {
            Mode::Sangria(args) => args.primary_circuit,
            Mode::Cyclefold(_) => Circuits::Trivial,
        }
    }
}

#[derive(Subcommand, Debug)]
pub enum Mode {
    /// IVC using Sangria (requires both primary and secondary circuit options)
    Sangria(SangriaArgs),
    /// IVC using Cyclefold (only a primary circuit is needed)
    Cyclefold(CyclefoldArgs),
}

#[derive(Parser, Debug)]
pub struct SangriaArgs {
    // Primary circuit options
    #[arg(value_enum, default_value_t = Circuits::Poseidon)]
    pub primary_circuit: Circuits,
    #[arg(long, default_value_t = 17)]
    pub primary_circuit_k_table_size: u32,
    #[arg(long, default_value_t = 21)]
    pub primary_commitment_key_size: usize,
    #[arg(long, default_value_t = 1)]
    pub primary_repeat_count: usize,
    // Primary circuit parameters used only in Sangria
    #[arg(long, default_value_t = 10)]
    pub primary_r_f: usize,
    #[arg(long, default_value_t = 10)]
    pub primary_r_p: usize,

    // Secondary circuit options (only used for Sangria)
    #[arg(value_enum, default_value_t = Circuits::Trivial)]
    pub secondary_circuit: Circuits,
    #[arg(long, default_value_t = 17)]
    pub secondary_circuit_k_table_size: u32,
    #[arg(long, default_value_t = 21)]
    pub secondary_commitment_key_size: usize,
    #[arg(long, default_value_t = 1)]
    pub secondary_repeat_count: usize,
    #[arg(long, default_value_t = 10)]
    pub secondary_r_f: usize,
    #[arg(long, default_value_t = 10)]
    pub secondary_r_p: usize,
}

#[derive(Parser, Debug)]
pub struct CyclefoldArgs {
    #[arg(value_enum, default_value_t = Circuits::Poseidon)]
    pub primary_circuit: Circuits,
    #[arg(long, default_value_t = 20)]
    pub primary_circuit_k_table_size: u32,
    #[arg(long, default_value_t = 25)]
    pub primary_commitment_key_size: usize,
    #[arg(long, default_value_t = 1)]
    pub primary_repeat_count: usize,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
pub enum Circuits {
    Poseidon,
    Trivial,
    MerkleTree,
}

impl Args {
    fn build_log_filename(&self) -> Option<PathBuf> {
        if !self.file_logs {
            return None;
        }

        let fold_step_count = self.fold_step_count;
        match &self.mode {
            Mode::Sangria(SangriaArgs {
                primary_circuit,
                primary_repeat_count,
                secondary_circuit,
                secondary_repeat_count,
                ..
            }) => Some(build_log_folder().join(format!(
                "sirius_sangria_{primary_circuit}-{primary_repeat_count}_{secondary_circuit}-{secondary_repeat_count}_{fold_step_count}.log"
            ))),
            Mode::Cyclefold(CyclefoldArgs {
                primary_circuit,
                primary_repeat_count,
                ..
            }) => Some(build_log_folder().join(format!(
                "sirius_cyclefold_{primary_circuit}-{primary_repeat_count}_{fold_step_count}.log"
            ))),
        }
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
            println!(
                "The logs will be written to the file: {}",
                log_filename.to_string_lossy()
            );
        } else if self.json_logs {
            builder.json().init();
        } else {
            builder.init();
        }

        info!("start with args: {self:?}");
    }
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

impl fmt::Display for Circuits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Poseidon => "poseidon",
                Self::Trivial => "trivial",
                Self::MerkleTree => "merkle",
            }
        )
    }
}

use bn256::G1 as C1;
use grumpkin::G1 as C2;
use halo2curves::{bn256, grumpkin};

const MAIN_GATE_SIZE: usize = 5;
const RATE: usize = 4;

type RandomOracle = sirius::poseidon::PoseidonRO<MAIN_GATE_SIZE, RATE>;
type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

type C1Affine = <C1 as halo2curves::group::prime::PrimeCurve>::Affine;
type C1Scalar = <C1 as halo2curves::group::Group>::Scalar;

type C2Affine = <C2 as halo2curves::group::prime::PrimeCurve>::Affine;
type C2Scalar = <C2 as halo2curves::group::Group>::Scalar;

trait TestCircuitHelpers<F: PrimeField> {
    const NAME: &'static str;

    fn get_default_input() -> F {
        F::ZERO
    }

    fn update_between_step(&mut self) {}
}

impl<F: PrimeField, const ARITY: usize> TestCircuitHelpers<F> for trivial::Circuit<ARITY, F> {
    const NAME: &'static str = "Trivial";
}
impl<F: PrimeFieldBits> TestCircuitHelpers<F> for TestPoseidonCircuit<F> {
    const NAME: &'static str = "Poseidon";
}
impl<F> TestCircuitHelpers<F> for MerkleTreeUpdateCircuit<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    const NAME: &'static str = "MerkleTree";

    fn get_default_input() -> F {
        *Tree::default().get_root()
    }

    #[instrument("update_leaves", skip_all)]
    fn update_between_step(&mut self) {
        assert!(self.pop_front_proof_batch())
    }
}

fn fold<
    SC1: StepCircuit<1, C1Scalar> + TestCircuitHelpers<C1Scalar>,
    SC2: StepCircuit<1, C2Scalar> + TestCircuitHelpers<C2Scalar>,
>(
    args: &Args,
    mut primary: SC1,
    mut secondary: SC2,
) {
    let _span = info_span!("cli", primary = SC1::NAME, secondary = SC2::NAME).entered();

    let primary_commitment_key = poseidon::get_or_create_commitment_key::<C1Affine>(
        args.primary_commitment_key_size(),
        "bn256",
    )
    .expect("Failed to get primary key");
    let secondary_commitment_key = poseidon::get_or_create_commitment_key::<C2Affine>(
        args.secondary_commitment_key_size(),
        "grumpkin",
    )
    .expect("Failed to get secondary key");

    match &args.mode {
        Mode::Sangria(sangria_args) => {
            // Specifications for random oracle used as part of the IVC algorithm
            let primary_spec = RandomOracleConstant::<C1Scalar>::new(
                sangria_args.primary_r_f,
                sangria_args.primary_r_p,
            );
            let secondary_spec = RandomOracleConstant::<C2Scalar>::new(
                sangria_args.secondary_r_f,
                sangria_args.secondary_r_p,
            );

            let pp = sangria::PublicParams::<
                '_,
                1,
                1,
                MAIN_GATE_SIZE,
                C1Affine,
                C2Affine,
                _,
                _,
                RandomOracle,
                RandomOracle,
            >::new(
                sangria::CircuitPublicParamsInput::new(
                    sangria_args.primary_circuit_k_table_size,
                    &primary_commitment_key,
                    primary_spec,
                    &primary,
                ),
                sangria::CircuitPublicParamsInput::new(
                    sangria_args.secondary_circuit_k_table_size,
                    &secondary_commitment_key,
                    secondary_spec,
                    &secondary,
                ),
                args.limb_width,
                args.limbs_count,
            )
            .unwrap();

            let primary_input = SC1::get_default_input();
            let secondary_input = SC2::get_default_input();

            let prove_span = info_span!("prove", steps = args.fold_step_count.get()).entered();

            let mut ivc = sangria::IVC::new(
                &pp,
                &primary,
                [primary_input],
                &secondary,
                [secondary_input],
                args.debug_mode,
            )
            .unwrap();

            for _step in 1..args.fold_step_count.into() {
                primary.update_between_step();
                secondary.update_between_step();

                ivc.fold_step(&pp, &primary, &secondary).unwrap();
            }
            prove_span.exit();

            ivc.verify(&pp).unwrap()
        }
        Mode::Cyclefold(cyclefold_args) => {
            let mut pp = cyclefold::PublicParams::new(
                &primary,
                primary_commitment_key,
                secondary_commitment_key,
                cyclefold_args.primary_circuit_k_table_size,
            )
            .unwrap();

            let primary_input = SC1::get_default_input();

            let prove_span = info_span!("prove", steps = args.fold_step_count.get()).entered();

            let mut ivc =
                cyclefold::IVC::new(&mut pp, &primary, [primary_input]).expect("while step=0");

            for step in 1..args.fold_step_count.into() {
                primary.update_between_step();

                ivc = ivc
                    .next(&pp, &primary)
                    .unwrap_or_else(|err| panic!("while step={step}: {err:?}"));
            }

            prove_span.exit();

            ivc.verify(&pp).expect("while verify");
        }
    }
}

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    let args = Args::parse();

    args.init_logger();

    // To osterize the total execution time of the example

    // Such a redundant call design due to the fact that they are different function types for the
    // compiler due to generics
    let mut rng = rand::thread_rng();
    match (args.primary_circuit(), args.secondary_circuit()) {
        (Circuits::Poseidon, Circuits::Trivial) => fold(
            &args,
            TestPoseidonCircuit::new(args.primary_repeat_count()),
            trivial::Circuit::default(),
        ),
        (Circuits::Poseidon, Circuits::Poseidon) => fold(
            &args,
            TestPoseidonCircuit::new(args.primary_repeat_count()),
            TestPoseidonCircuit::new(args.secondary_repeat_count()),
        ),
        (Circuits::Trivial, Circuits::Poseidon) => fold(
            &args,
            trivial::Circuit::default(),
            TestPoseidonCircuit::new(args.secondary_repeat_count()),
        ),
        (Circuits::Trivial, Circuits::Trivial) => fold(
            &args,
            trivial::Circuit::default(),
            trivial::Circuit::default(),
        ),
        (Circuits::MerkleTree, Circuits::Trivial) => fold(
            &args,
            merkle::MerkleTreeUpdateCircuit::new_with_random_updates(
                &mut rng,
                args.primary_repeat_count(),
                args.fold_step_count.get(),
            ),
            trivial::Circuit::default(),
        ),
        (Circuits::MerkleTree, Circuits::Poseidon) => fold(
            &args,
            merkle::MerkleTreeUpdateCircuit::new_with_random_updates(
                &mut rng,
                args.primary_repeat_count(),
                args.fold_step_count.get(),
            ),
            TestPoseidonCircuit::new(args.secondary_repeat_count()),
        ),
        (Circuits::Poseidon, Circuits::MerkleTree) => fold(
            &args,
            TestPoseidonCircuit::new(args.primary_repeat_count()),
            merkle::MerkleTreeUpdateCircuit::new_with_random_updates(
                &mut rng,
                args.secondary_repeat_count(),
                args.fold_step_count.get(),
            ),
        ),
        (Circuits::Trivial, Circuits::MerkleTree) => fold(
            &args,
            trivial::Circuit::default(),
            merkle::MerkleTreeUpdateCircuit::new_with_random_updates(
                &mut rng,
                args.secondary_repeat_count(),
                args.fold_step_count.get(),
            ),
        ),
        (Circuits::MerkleTree, Circuits::MerkleTree) => fold(
            &args,
            merkle::MerkleTreeUpdateCircuit::new_with_random_updates(
                &mut rng,
                args.primary_repeat_count(),
                args.fold_step_count.get(),
            ),
            merkle::MerkleTreeUpdateCircuit::new_with_random_updates(
                &mut rng,
                args.secondary_repeat_count(),
                args.fold_step_count.get(),
            ),
        ),
    }
}
