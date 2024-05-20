#![allow(dead_code)]

use std::{array, io, num::NonZeroUsize, path::Path};

use criterion::{black_box, criterion_group, Criterion};
use ff::Field;
use halo2_gadgets::sha256::BLOCK_SIZE;

use halo2curves::{bn256, grumpkin, CurveAffine, CurveExt};

use bn256::G1 as C1;
use grumpkin::G1 as C2;

use metadata::LevelFilter;
use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit, CircuitPublicParamsInput, PublicParams, IVC},
    poseidon::{self, ROPair},
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

const ARITY: usize = BLOCK_SIZE / 2;

const CIRCUIT_TABLE_SIZE1: usize = 17;
const CIRCUIT_TABLE_SIZE2: usize = 17;
const COMMITMENT_KEY_SIZE: usize = 20;

const T: usize = 5;
const RATE: usize = 4;

type RandomOracle = poseidon::PoseidonRO<T, RATE>;

type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

type C1Affine = <C1 as halo2curves::group::prime::PrimeCurve>::Affine;
type C2Affine = <C2 as halo2curves::group::prime::PrimeCurve>::Affine;

type C1Scalar = <C1 as halo2curves::group::Group>::Scalar;
type C2Scalar = <C2 as halo2curves::group::Group>::Scalar;

const FOLDER: &str = ".cache/examples";

#[instrument]
fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    unsafe { CommitmentKey::load_or_setup_cache(Path::new(FOLDER), label, k) }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    let _span = info_span!("trivial_bench").entered();
    let prepare_span = info_span!("prepare").entered();

    // C1
    let sc1 = step_circuit::trivial::Circuit::<ARITY, _>::default();
    // C2
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
        step_circuit::trivial::Circuit<ARITY, _>,
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

    let mut group = c.benchmark_group("ivc_of_trivial");
    group.significance_level(0.1).sample_size(15);

    group.bench_function("fold_1_step", |b| {
        let mut rnd = rand::thread_rng();
        let primary_z_0 = array::from_fn(|_| C1Scalar::random(&mut rnd));
        let secondary_z_0 = array::from_fn(|_| C2Scalar::random(&mut rnd));

        b.iter(|| {
            IVC::fold(
                &pp,
                sc1.clone(),
                black_box(primary_z_0),
                sc2.clone(),
                black_box(secondary_z_0),
                NonZeroUsize::new(1).unwrap(),
            )
            .unwrap();
        })
    });

    group.bench_function("fold_2_step", |b| {
        let mut rnd = rand::thread_rng();
        let primary_z_0 = array::from_fn(|_| C1Scalar::random(&mut rnd));
        let secondary_z_0 = array::from_fn(|_| C2Scalar::random(&mut rnd));

        b.iter(|| {
            IVC::fold(
                &pp,
                sc1.clone(),
                black_box(primary_z_0),
                sc2.clone(),
                black_box(secondary_z_0),
                NonZeroUsize::new(2).unwrap(),
            )
            .unwrap();
        })
    });

    group.finish();
}

criterion_group!(benches, criterion_benchmark);

fn main() {
    tracing_subscriber::fmt()
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        )
        .json()
        .init();

    benches();

    criterion::Criterion::default()
        .configure_from_args()
        .final_summary();
}
