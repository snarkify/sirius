use std::{array, num::NonZeroUsize};

use clap::{Parser, ValueEnum};

#[allow(dead_code)]
mod poseidon;

use ff::Field;
use poseidon::poseidon_step_circuit::TestPoseidonCircuit;
use sirius::{
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
}

use halo2curves::{bn256, grumpkin};

use bn256::G1 as C1;
use grumpkin::G1 as C2;

const MAIN_GATE_SIZE: usize = 5;
const RATE: usize = 4;

type RandomOracle = sirius::poseidon::PoseidonRO<MAIN_GATE_SIZE, RATE>;
type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

type C1Affine = <C1 as halo2curves::group::prime::PrimeCurve>::Affine;
type C1Scalar = <C1 as halo2curves::group::Group>::Scalar;

type C2Affine = <C2 as halo2curves::group::prime::PrimeCurve>::Affine;
type C2Scalar = <C2 as halo2curves::group::Group>::Scalar;

fn fold(
    args: &Args,
    primary: impl StepCircuit<1, C1Scalar>,
    secondary: impl StepCircuit<1, C2Scalar>,
) {
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

    let mut rnd = rand::thread_rng();
    let primary_input = array::from_fn(|_| C1Scalar::random(&mut rnd));
    let secondary_input = array::from_fn(|_| C2Scalar::random(&mut rnd));

    if args.debug_mode {
        IVC::fold_with_debug_mode(
            &pp,
            primary,
            primary_input,
            secondary,
            secondary_input,
            args.fold_step_count,
        )
        .unwrap();
    } else {
        IVC::fold(
            &pp,
            primary,
            primary_input,
            secondary,
            secondary_input,
            args.fold_step_count,
        )
        .unwrap();
    }
}

fn main() {
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
    let _span = info_span!("poseidon_example").entered();

    // Such a redundant call design due to the fact that they are different function types for the
    // compiler due to generics
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
    }
}
