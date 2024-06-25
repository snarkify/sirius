#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

use std::num::NonZeroUsize;

use clap::{Parser, ValueEnum};

#[allow(dead_code)]
mod poseidon;

#[allow(dead_code)]
mod merkle;

use ff::{FromUniformBytes, PrimeField, PrimeFieldBits};
use merkle::MerkleTreeUpdateCircuit;
use poseidon::poseidon_step_circuit::TestPoseidonCircuit;
use sirius::{
    gadgets::merkle_tree::off_circuit::Tree,
    ivc::{step_circuit::trivial, CircuitPublicParamsInput, PublicParams, StepCircuit, IVC},
    poseidon::ROPair,
};
use tracing::*;
use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(value_enum, default_value_t = Circuits::Poseidon)       ]
    primary_circuit: Circuits,
    #[arg(long, default_value_t = 17)]
    primary_circuit_k_table_size: u32,
    #[arg(long, default_value_t = 21)]
    primary_commitment_key_size: usize,
    #[arg(long, default_value_t = 1)]
    primary_repeat_count: usize,
    #[arg(long, default_value_t = 1)]
    primary_batch_size: usize,
    #[arg(long, default_value_t = 10)]
    primary_r_f: usize,
    #[arg(long, default_value_t = 10)]
    primary_r_p: usize,
    #[arg(value_enum, default_value_t = Circuits::Trivial)        ]
    secondary_circuit: Circuits,
    #[arg(long, default_value_t = 17)]
    secondary_circuit_k_table_size: u32,
    #[arg(long, default_value_t = 21)]
    secondary_commitment_key_size: usize,
    #[arg(long, default_value_t = 1)]
    secondary_repeat_count: usize,
    #[arg(long, default_value_t = 10)]
    secondary_r_f: usize,
    #[arg(long, default_value_t = 10)]
    secondary_r_p: usize,
    #[arg(long, default_value_t = NonZeroUsize::new(32).unwrap()) ]
    limb_width: NonZeroUsize,
    #[arg(long, default_value_t = NonZeroUsize::new(10).unwrap()) ]
    limbs_count: NonZeroUsize,
    #[arg(long, default_value_t = false)]
    debug_mode: bool,
    #[arg(long, default_value_t = NonZeroUsize::new(1).unwrap())  ]
    fold_step_count: NonZeroUsize,
    #[arg(long, default_value_t = false)]
    json_logs: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
enum Circuits {
    Poseidon,
    Trivial,
    MerkleTree,
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

    fn update_between_step(&mut self) {
        self.random_update_leaves(&mut rand::thread_rng());
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
        args.primary_commitment_key_size,
        "bn256",
    )
    .expect("Failed to get primary key");
    let secondary_commitment_key = poseidon::get_or_create_commitment_key::<C2Affine>(
        args.secondary_commitment_key_size,
        "grumpkin",
    )
    .expect("Failed to get secondary key");

    // Specifications for random oracle used as part of the IVC algorithm
    let primary_spec = RandomOracleConstant::<C1Scalar>::new(args.primary_r_f, args.primary_r_p);
    let secondary_spec =
        RandomOracleConstant::<C2Scalar>::new(args.secondary_r_f, args.secondary_r_p);

    let pp = PublicParams::<
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
        CircuitPublicParamsInput::new(
            args.primary_circuit_k_table_size,
            &primary_commitment_key,
            primary_spec,
            &primary,
        ),
        CircuitPublicParamsInput::new(
            args.secondary_circuit_k_table_size,
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

    let mut ivc = IVC::new(
        &pp,
        &primary,
        [primary_input],
        &secondary,
        [secondary_input],
        args.debug_mode,
    )
    .unwrap();

    for _step in 0..args.fold_step_count.into() {
        primary.update_between_step();
        secondary.update_between_step();

        ivc.fold_step(&pp, &primary, &secondary).unwrap();
    }
    prove_span.exit();

    ivc.verify(&pp).unwrap()
}

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    let args = Args::parse();

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
    if args.json_logs {
        builder.json().init();
    } else {
        builder.init();
    }

    // To osterize the total execution time of the example

    // Such a redundant call design due to the fact that they are different function types for the
    // compiler due to generics
    let mut rng = rand::thread_rng();
    match (args.primary_circuit, args.secondary_circuit) {
        (Circuits::Poseidon, Circuits::Trivial) => fold(
            &args,
            TestPoseidonCircuit::new(args.primary_repeat_count),
            trivial::Circuit::default(),
        ),
        (Circuits::Poseidon, Circuits::Poseidon) => fold(
            &args,
            TestPoseidonCircuit::new(args.primary_repeat_count),
            TestPoseidonCircuit::new(args.secondary_repeat_count),
        ),
        (Circuits::Trivial, Circuits::Poseidon) => fold(
            &args,
            trivial::Circuit::default(),
            TestPoseidonCircuit::new(args.secondary_repeat_count),
        ),
        (Circuits::Trivial, Circuits::Trivial) => fold(
            &args,
            trivial::Circuit::default(),
            trivial::Circuit::default(),
        ),
        (Circuits::MerkleTree, Circuits::Trivial) => fold(
            &args,
            merkle::MerkleTreeUpdateCircuit::new_with_random_update(
                args.primary_repeat_count,
                &mut rng,
            ),
            trivial::Circuit::default(),
        ),
        (Circuits::MerkleTree, Circuits::Poseidon) => fold(
            &args,
            merkle::MerkleTreeUpdateCircuit::new_with_random_update(
                args.primary_repeat_count,
                &mut rng,
            ),
            TestPoseidonCircuit::new(args.secondary_repeat_count),
        ),
        (Circuits::Poseidon, Circuits::MerkleTree) => fold(
            &args,
            TestPoseidonCircuit::new(args.primary_repeat_count),
            merkle::MerkleTreeUpdateCircuit::new_with_random_update(
                args.secondary_repeat_count,
                &mut rng,
            ),
        ),
        (Circuits::Trivial, Circuits::MerkleTree) => fold(
            &args,
            trivial::Circuit::default(),
            merkle::MerkleTreeUpdateCircuit::new_with_random_update(
                args.secondary_repeat_count,
                &mut rng,
            ),
        ),
        (Circuits::MerkleTree, Circuits::MerkleTree) => fold(
            &args,
            merkle::MerkleTreeUpdateCircuit::new_with_random_update(
                args.primary_repeat_count,
                &mut rng,
            ),
            merkle::MerkleTreeUpdateCircuit::new_with_random_update(
                args.secondary_repeat_count,
                &mut rng,
            ),
        ),
    }
}
