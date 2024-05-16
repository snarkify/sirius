use std::{array, io, iter, marker::PhantomData, num::NonZeroUsize, path::Path};

use criterion::{black_box, criterion_group, Criterion};
use ff::{Field, FromUniformBytes, PrimeFieldBits};

use halo2curves::{bn256, grumpkin, CurveAffine, CurveExt};

use metadata::LevelFilter;

use bn256::G1 as C1;
use grumpkin::G1 as C2;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::ConstraintSystem,
};
use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit, CircuitPublicParamsInput, PublicParams, StepCircuit, SynthesisError, IVC},
    main_gate::{MainGate, MainGateConfig, RegionCtx, WrapValue},
    poseidon::{self, poseidon_circuit::PoseidonChip, ROPair, Spec},
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

const ARITY: usize = 1;

const CIRCUIT_TABLE_SIZE1: usize = 21;
const CIRCUIT_TABLE_SIZE2: usize = 20;
const COMMITMENT_KEY_SIZE: usize = 27;

// Spec for user defined poseidon circuit
const T1: usize = 3;
const RATE1: usize = 2;
const R_F1: usize = 4;
const R_P1: usize = 3;

#[derive(Clone, Debug)]
struct TestPoseidonCircuitConfig {
    pconfig: MainGateConfig<T1>,
}

#[derive(Debug, Clone)]
struct TestPoseidonCircuit<F: PrimeFieldBits> {
    repeat_count: usize,
    _p: PhantomData<F>,
}
impl<F: PrimeFieldBits> Default for TestPoseidonCircuit<F> {
    fn default() -> Self {
        Self {
            repeat_count: 1,
            _p: Default::default(),
        }
    }
}

impl<F: PrimeFieldBits> TestPoseidonCircuit<F> {
    pub fn new(repeat_count: usize) -> Self {
        Self {
            repeat_count,
            _p: Default::default(),
        }
    }
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

        layouter
            .assign_region(
                || "poseidon hash",
                move |region| {
                    let mut z_i = z_in.clone();
                    let ctx = &mut RegionCtx::new(region, 0);

                    for step in 0..=self.repeat_count {
                        let mut pchip = PoseidonChip::new(config.pconfig.clone(), spec.clone());

                        pchip.update(
                            &z_i.iter()
                                .cloned()
                                .map(WrapValue::Assigned)
                                .collect::<Vec<WrapValue<F>>>(),
                        );

                        info!(
                            "offset for {} hash repeat count is {} (log2 = {})",
                            step,
                            ctx.offset(),
                            (ctx.offset() as f64).log2()
                        );

                        z_i = [pchip.squeeze(ctx).inspect_err(|err| {
                            error!("at step {step}: {err:?}");
                        })?];
                    }

                    info!(
                        "total offset for {} hash repeat count is {} (log2 = {})",
                        self.repeat_count,
                        ctx.offset(),
                        (ctx.offset() as f64).log2()
                    );

                    Ok(z_i)
                },
            )
            .map_err(|err| {
                error!("while synth {err:?}");
                SynthesisError::Halo2(err)
            })
    }
}

// specs for IVC circuit
const T: usize = 5;
const RATE: usize = 4;

type RandomOracle = poseidon::PoseidonRO<T, RATE>;

type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

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
    let _span = info_span!("poseidon_bench").entered();
    let prepare_span = info_span!("prepare").entered();

    // C1
    let sc1 = TestPoseidonCircuit::default();
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
        TestPoseidonCircuit<_>,
        step_circuit::trivial::Circuit<ARITY, _>,
        RandomOracle,
        RandomOracle,
    >::new(
        CircuitPublicParamsInput::new(
            CIRCUIT_TABLE_SIZE1 as u32,
            &primary_commitment_key,
            primary_spec,
            &sc1,
        ),
        CircuitPublicParamsInput::new(
            CIRCUIT_TABLE_SIZE2 as u32,
            &secondary_commitment_key,
            secondary_spec,
            &sc2,
        ),
        LIMB_WIDTH,
        LIMBS_COUNT,
    )
    .unwrap();

    prepare_span.exit();

    let mut group = c.benchmark_group(format!("ivc_of_poseidon with k={CIRCUIT_TABLE_SIZE1}"));
    group.significance_level(0.1).sample_size(15);

    for repeat_count in (0..=87_380).rev().step_by(600).chain(iter::once(0)) {
        let mut rnd = rand::thread_rng();
        let primary_z_0 = array::from_fn(|_| C1Scalar::random(&mut rnd));
        let secondary_z_0 = array::from_fn(|_| C2Scalar::random(&mut rnd));

        group.bench_with_input(
            criterion::BenchmarkId::new(
                format!("fold step with repeated hashed {repeat_count} & k"),
                ((24 * repeat_count) as f64).log2(),
            ),
            &repeat_count,
            |b, repeat_count| {
                let sc1 = TestPoseidonCircuit::new(*repeat_count);

                let mut ivc = IVC::new(
                    &pp,
                    sc1,
                    black_box(primary_z_0),
                    sc2.clone(),
                    black_box(secondary_z_0),
                    false,
                )
                .unwrap();

                b.iter(|| {
                    let _span =
                        info_span!("bench_fold_step", repeat_count = repeat_count).entered();
                    ivc.fold_step(&pp).unwrap();
                })
            },
        );
    }

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
