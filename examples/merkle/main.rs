use std::{env, io, num::NonZeroUsize, path::Path};

use bn256::G1 as C1;
use grumpkin::G1 as C2;
use sirius::{
    commitment::CommitmentKey,
    halo2curves::{bn256, ff::Field, grumpkin, CurveAffine, CurveExt},
    ivc::{step_circuit, CircuitPublicParamsInput, PublicParams, IVC},
    poseidon::ROPair,
};
use tracing::info_span;

pub mod circuit;
mod merkle_tree_gadget;

use circuit::MerkleTreeUpdateCircuit;
use merkle_tree_gadget::{off_circuit::Tree, *};
use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

type C1Affine = <C1 as sirius::halo2curves::group::prime::PrimeCurve>::Affine;
type C2Affine = <C2 as sirius::halo2curves::group::prime::PrimeCurve>::Affine;

pub type C1Scalar = <C1 as sirius::halo2curves::group::Group>::Scalar;
type C2Scalar = <C2 as sirius::halo2curves::group::Group>::Scalar;

type RandomOracle = sirius::poseidon::PoseidonRO<T, RATE>;
type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

const COMMITMENT_KEY_SIZE: usize = 23;

const ARITY: usize = 1;

const CIRCUIT_TABLE_SIZE1: usize = 17;
const CIRCUIT_TABLE_SIZE2: usize = 17;

fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    const FOLDER: &str = ".cache/examples";

    unsafe { CommitmentKey::load_or_setup_cache(Path::new(FOLDER), label, k) }
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

    let mut rng = rand::thread_rng();

    let _span = info_span!("merkle_example").entered();
    let prepare_span = info_span!("prepare").entered();

    let step_count = NonZeroUsize::new(2).unwrap();
    let mut sc1 = MerkleTreeUpdateCircuit::new_with_random_updates(&mut rng, 1, step_count.get());

    let sc2 = step_circuit::trivial::Circuit::<ARITY, _>::default();

    let primary_spec = RandomOracleConstant::<<C1 as CurveExt>::ScalarExt>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<<C2 as CurveExt>::ScalarExt>::new(10, 10);

    let primary_commitment_key =
        get_or_create_commitment_key::<bn256::G1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get secondary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<grumpkin::G1Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get primary key");

    let pp = PublicParams::<
        '_,
        ARITY,
        ARITY,
        T,
        C1Affine,
        C2Affine,
        MerkleTreeUpdateCircuit<_>,
        step_circuit::trivial::Circuit<ARITY, _>,
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

    for _ in 0..step_count.get() {
        sc1.pop_front_proof_batch();
        ivc.fold_step(&pp, &sc1, &sc2).unwrap();
    }

    ivc.verify(&pp).unwrap();
}
