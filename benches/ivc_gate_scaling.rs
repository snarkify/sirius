//! Benchmark for comparing the dependency of sangria::IVC and cyclefold::IVC on the GATES_COUNT parameter.
//!
//! This benchmark implements a multi-step circuit where the number of gates (i.e. circuit duplications)
//! is hardcoded per benchmark run. Separate sets of GATES_COUNT values are used for Sangria and Cyclefold.

use std::{array, convert::TryInto, marker::PhantomData, path::Path};

use criterion::{criterion_group, criterion_main, Criterion};
use itertools::multizip;
use sirius::{
    commitment::CommitmentKey,
    ff::PrimeField,
    gadgets::poseidon_step_circuit::TestPoseidonCircuit,
    halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::{self, ConstraintSystem},
    },
    halo2curves::{bn256, grumpkin, CurveAffine},
    ivc::{self, cyclefold, sangria, StepCircuit, SynthesisError},
};
use tracing::info_span;

/// Base arity for the step circuit.
const BASE_ARITY: usize = 1;
/// Number of fold steps to perform in the IVC.
const FOLD_STEP_COUNT: usize = 1;

/// A multi-step circuit that composes an array of sub-circuits.
/// It is parameterized by:
///  - BASE_ARITY: the arity of each step circuit,
///  - REPEATS: the number of times the step circuit is duplicated,
///  - OVERALL_ARITY: must equal BASE_ARITY * REPEATS.
#[derive(Clone, Debug)]
pub struct MultiStepCircuit<
    CIRCUIT,
    const BASE_ARITY: usize,
    const REPEATS: usize,
    const OVERALL_ARITY: usize,
    F: PrimeField,
> {
    pub circuits: [CIRCUIT; REPEATS],
    _marker: PhantomData<F>,
}

impl<T, const BASE_ARITY: usize, const REPEATS: usize, const OVERALL_ARITY: usize, F>
    MultiStepCircuit<T, BASE_ARITY, REPEATS, OVERALL_ARITY, F>
where
    F: PrimeField,
{
    pub fn new(circuits: [T; REPEATS]) -> Self {
        assert_eq!(
            OVERALL_ARITY,
            BASE_ARITY * REPEATS,
            "OVERALL_ARITY must equal BASE_ARITY * REPEATS"
        );
        Self {
            circuits,
            _marker: PhantomData,
        }
    }
}

impl<T, const BASE_ARITY: usize, const REPEATS: usize, const OVERALL_ARITY: usize, F>
    StepCircuit<OVERALL_ARITY, F> for MultiStepCircuit<T, BASE_ARITY, REPEATS, OVERALL_ARITY, F>
where
    F: PrimeField,
    T: StepCircuit<BASE_ARITY, F> + Clone,
    T::Config: Clone,
{
    type Config = [T::Config; REPEATS];

    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        assert_eq!(
            OVERALL_ARITY,
            BASE_ARITY * REPEATS,
            "OVERALL_ARITY must equal BASE_ARITY * REPEATS"
        );
        array::from_fn(|_i| T::configure(cs))
    }

    fn synthesize_step(
        &self,
        configs: Self::Config,
        layouter: &mut impl Layouter<F>,
        z_in: &[AssignedCell<F, F>; OVERALL_ARITY],
    ) -> Result<[AssignedCell<F, F>; OVERALL_ARITY], SynthesisError> {
        assert_eq!(
            OVERALL_ARITY,
            BASE_ARITY * REPEATS,
            "OVERALL_ARITY must equal BASE_ARITY * REPEATS"
        );
        let mut out_cells: Vec<AssignedCell<F, F>> = Vec::with_capacity(OVERALL_ARITY);
        for (circuit, cfg, z_chunk) in multizip((
            self.circuits.iter(),
            configs.into_iter(),
            z_in.chunks_exact(BASE_ARITY),
        )) {
            let z_chunk_arr: [AssignedCell<F, F>; BASE_ARITY] = z_chunk
                .to_vec()
                .try_into()
                .map_err(|_| SynthesisError::Halo2(plonk::Error::Synthesis))?;
            let out_chunk = circuit.synthesize_step(cfg, layouter, &z_chunk_arr)?;
            out_cells.extend_from_slice(&out_chunk);
        }
        out_cells
            .try_into()
            .map_err(|_| SynthesisError::Halo2(plonk::Error::Synthesis))
    }
}

/// IVC mode used in the benchmark.
#[derive(Clone, Copy, Debug)]
pub enum Mode {
    Sangria,
    Cyclefold,
}

/// Helper to get or create a commitment key.
/// This is a simplified version for benchmarking purposes.
fn get_or_create_commitment_key<C: CurveAffine>(k: usize, label: &'static str) -> CommitmentKey<C> {
    const CACHE_FOLDER: &str = ".cache/examples";
    unsafe {
        CommitmentKey::load_or_setup_cache(Path::new(CACHE_FOLDER), label, k)
            .expect("failed to get key")
    }
}

/// Macro for benchmarking Sangria.
/// Performs all heavy setup (circuit creation, public parameter generation, etc.) outside the measurement,
/// and then inside `b.iter` only creates a new IVC and folds it.
macro_rules! bench_sangria {
    ($group:expr, $gates:expr, $k:expr) => {{
        let bench_name = format!("Sangria_gates_{}", $gates);
        // OVERALL_ARITY = BASE_ARITY * $gates.
        const OVERALL_ARITY: usize = $gates * BASE_ARITY;
        // Build an array of step circuits.
        let circuits = array::from_fn(|_| TestPoseidonCircuit::<bn256::Fr>::default());
        let multi_circuit =
            MultiStepCircuit::<_, BASE_ARITY, $gates, OVERALL_ARITY, bn256::Fr>::new(circuits);

        // Create an input for the multi-step circuit.
        let z_in = array::from_fn(|i| bn256::Fr::from(i as u64));

        // Get commitment keys.
        let primary_commitment_key = get_or_create_commitment_key::<bn256::G1Affine>(25, "bn256");
        let secondary_commitment_key =
            get_or_create_commitment_key::<grumpkin::G1Affine>(25, "grumpkin");

        // Create public parameters and other inputs before the timed section.
        let _ = info_span!("sangria", gates_count = $gates).entered();
        let pp = sirius::sangria_prelude::bn256::new_default_pp::<OVERALL_ARITY, _, 1, _>(
            $k,
            &primary_commitment_key,
            &multi_circuit,
            17,
            &secondary_commitment_key,
            &ivc::step_circuit::trivial::Circuit::default(),
        );
        let trivial_input = array::from_fn(|i| bn256::Fq::from(i as u64));

        $group.bench_function(&bench_name, |b| {
            b.iter(|| {
                let _ = info_span!("bench_sangria", gates_count = $gates).entered();
                // Only the IVC creation and fold steps are measured.
                let mut ivc = sangria::IVC::new(
                    &pp,
                    &multi_circuit,
                    z_in,
                    &ivc::step_circuit::trivial::Circuit::default(),
                    trivial_input,
                    false,
                )
                .expect("Failed to create Sangria IVC");
                for _ in 0..FOLD_STEP_COUNT {
                    ivc.fold_step(
                        &pp,
                        &multi_circuit,
                        &ivc::step_circuit::trivial::Circuit::default(),
                    )
                    .expect("Sangria fold step failed");
                }
            });
        });
    }};
}

/// Macro for benchmarking Cyclefold.
/// Performs all heavy setup (circuit creation, public parameter generation, etc.) outside the measurement,
/// and then inside `b.iter` only creates a new IVC and runs the next (fold) steps.
macro_rules! bench_cyclefold {
    ($group:expr, $gates:expr, $k:expr) => {{
        let bench_name = format!("Cyclefold_gates_{}", $gates);
        const OVERALL_ARITY: usize = $gates * BASE_ARITY;
        // Build an array of step circuits.
        let circuits = array::from_fn(|_| TestPoseidonCircuit::<bn256::Fr>::default());
        let multi_circuit =
            MultiStepCircuit::<_, BASE_ARITY, $gates, OVERALL_ARITY, bn256::Fr>::new(circuits);

        // Create an input for the multi-step circuit.
        let z_in = array::from_fn(|i| bn256::Fr::from(i as u64));

        // Get commitment keys.
        let primary_commitment_key = get_or_create_commitment_key::<bn256::G1Affine>(25, "bn256");
        let secondary_commitment_key =
            get_or_create_commitment_key::<grumpkin::G1Affine>(25, "grumpkin");

        // Create public parameters before the timed section.
        let _ = info_span!("cyclefold", gates_count = $gates).entered();
        let mut pp = cyclefold::PublicParams::new(
            &multi_circuit,
            primary_commitment_key,
            secondary_commitment_key,
            $k,
        )
        .expect("Failed to create Cyclefold public params");

        $group.bench_function(&bench_name, |b| {
            b.iter(|| {
                let _ = info_span!("bench_cyclefold", gates_count = $gates).entered();
                let mut ivc = cyclefold::IVC::new(&mut pp, &multi_circuit, z_in)
                    .expect("Failed to create Cyclefold IVC");
                for _ in 0..FOLD_STEP_COUNT {
                    ivc = ivc
                        .next(&pp, &multi_circuit)
                        .expect("Cyclefold next step failed");
                }
            });
        });
    }};
}

/// The main benchmark function.
/// Uses separate macros for Sangria and Cyclefold benchmarks.
pub fn benchmark_ivc(c: &mut Criterion) {
    #[cfg(test)]
    {
        use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

        tracing_subscriber::fmt()
            // Adds events to track the entry and exit of the span, which are used to build time-profiling
            .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
            // Changes the default level to INFO
            .with_env_filter(
                EnvFilter::builder()
                    .with_default_directive(LevelFilter::DEBUG.into())
                    .from_env_lossy(),
            )
            .init();
    }

    // For Sangria, use these gate counts.
    {
        let mut group = c.benchmark_group("Sangria_IVC");
        bench_sangria!(group, 1, 20);
        bench_sangria!(group, 5, 22);
        bench_sangria!(group, 10, 24);
        group.finish();
    }

    // For Cyclefold, use these gate counts.
    {
        let mut group = c.benchmark_group("Cyclefold_IVC");
        bench_cyclefold!(group, 5, 21);
        bench_cyclefold!(group, 10, 21);
        bench_cyclefold!(group, 20, 22);
        bench_cyclefold!(group, 100, 22);
        group.finish();
    }
}

criterion_group!(benches, benchmark_ivc);
criterion_main!(benches);
