use std::{array, io, marker::PhantomData, path::Path};

use bn256::G1 as C1;
use criterion::{criterion_group, Criterion};
use metadata::LevelFilter;
use sirius::{
    commitment::CommitmentKey,
    ff::{Field, FromUniformBytes, PrimeFieldBits},
    group::Group,
    halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::ConstraintSystem,
    },
    halo2curves::{bn256, grumpkin, CurveAffine},
    ivc::{
        cyclefold::{PublicParams, IVC},
        StepCircuit, SynthesisError,
    },
    main_gate::{MainGate, MainGateConfig, RegionCtx, WrapValue},
    poseidon::{poseidon_circuit::PoseidonChip, Spec},
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

const ARITY: usize = 1;

const CIRCUIT_TABLE_SIZE1: usize = 17;
const COMMITMENT_KEY_SIZE: usize = 21;

// Spec for user defined poseidon circuit
const T1: usize = 3;
const RATE1: usize = 2;
const R_F1: usize = 4;
const R_P1: usize = 3;

#[derive(Clone, Debug)]
struct TestPoseidonCircuitConfig {
    pconfig: MainGateConfig<T1>,
}

#[derive(Default, Debug, Clone)]
struct TestPoseidonCircuit<F: PrimeFieldBits> {
    _p: PhantomData<F>,
}

impl<F: PrimeFieldBits + FromUniformBytes<64>> StepCircuit<ARITY, F> for TestPoseidonCircuit<F> {
    type Config = TestPoseidonCircuitConfig;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let pconfig = MainGate::configure(meta);
        Self::Config { pconfig }
    }

    fn synthesize_step(
        &self,
        config: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_in: &[AssignedCell<F, F>; ARITY],
    ) -> Result<[AssignedCell<F, F>; ARITY], SynthesisError> {
        let spec = Spec::<F, T1, RATE1>::new(R_F1, R_P1);
        let mut pchip = PoseidonChip::new(config.pconfig, spec);
        let input = z_in.iter().map(|x| x.into()).collect::<Vec<WrapValue<F>>>();
        pchip.update(&input);
        let output = layouter
            .assign_region(
                || "poseidon hash",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    pchip.squeeze(ctx)
                },
            )
            .map_err(SynthesisError::Halo2)?;
        Ok([output])
    }
}

type C1Scalar = <C1 as Group>::Scalar;

const FOLDER: &str = ".cache/examples";

#[instrument]
fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    unsafe { CommitmentKey::load_or_setup_cache(Path::new(FOLDER), label, k) }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    let _span = info_span!("poseidon_bench").entered();
    let prepare_span = info_span!("prepare").entered();

    // C1
    let sc1 = TestPoseidonCircuit::default();

    let primary_commitment_key =
        get_or_create_commitment_key::<bn256::G1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get secondary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<grumpkin::G1Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get primary key");

    let mut pp = PublicParams::new(
        &sc1,
        primary_commitment_key,
        secondary_commitment_key,
        CIRCUIT_TABLE_SIZE1 as u32,
    )
    .unwrap();

    prepare_span.exit();

    let mut group = c.benchmark_group("ivc_of_poseidon");
    group.significance_level(0.1).sample_size(10);

    group.bench_function("fold_1_step", |b| {
        let mut rnd = rand::thread_rng();
        let primary_z_0 = array::from_fn(|_| C1Scalar::random(&mut rnd));

        b.iter(|| {
            IVC::new(&mut pp, &sc1, primary_z_0)
                .expect("while step=0")
                .next(&pp, &sc1)
                .expect("while step=1")
                .verify(&pp)
                .expect("while verify");
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
