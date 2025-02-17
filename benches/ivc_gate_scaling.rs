//! Benchmark for comparing the dependency of sangria::IVC and cyclefold::IVC on the GATES_COUNT parameter.
//!
//! This benchmark implements a multi-step circuit where the number of gates (i.e. circuit duplications)
//! is hardcoded per benchmark run. Separate sets of GATES_COUNT values are used for Sangria and Cyclefold.

use std::{array, convert::TryInto, marker::PhantomData, path::Path};

use criterion::{criterion_group, criterion_main, Criterion};
use itertools::multizip;
use sirius::{
    commitment::CommitmentKey,
    ff::{FromUniformBytes, PrimeField},
    gadgets::poseidon_step_circuit::TestPoseidonCircuit,
    halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::{self, ConstraintSystem},
    },
    halo2curves::{bn256, grumpkin, CurveAffine},
    ivc::{self, cyclefold, sangria, StepCircuit, SynthesisError},
};

/// Base arity for the step circuit.
const BASE_ARITY: usize = 1;

/// Number of fold steps to perform in the IVC.
const FOLD_STEP_COUNT: usize = 5;

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

/// Runs an IVC instance using the given gate count and mode.
/// The gate count is provided as a const generic parameter.
fn run_ivc_with_gate_count<const GATES_COUNT: usize, const OVERALL_ARITY: usize>(mode: Mode)
where
    bn256::Fr: FromUniformBytes<64>,
{
    // OVERALL_ARITY = BASE_ARITY * GATES_COUNT.
    assert_eq!(OVERALL_ARITY, BASE_ARITY * GATES_COUNT);

    // Build an array of step circuits.
    let circuits = array::from_fn(|_| TestPoseidonCircuit::<bn256::Fr>::default());
    let multi_circuit =
        MultiStepCircuit::<_, BASE_ARITY, GATES_COUNT, OVERALL_ARITY, bn256::Fr>::new(circuits);

    // Create an input for the multi-step circuit.
    let z_in = array::from_fn(|i| bn256::Fr::from(i as u64));

    // Get commitment keys.
    let primary_commitment_key = get_or_create_commitment_key::<bn256::G1Affine>(25, "bn256");
    let secondary_commitment_key =
        get_or_create_commitment_key::<grumpkin::G1Affine>(25, "grumpkin");

    match mode {
        Mode::Sangria => {
            let pp = sirius::sangria_prelude::bn256::new_default_pp::<OVERALL_ARITY, _, 1, _>(
                17,
                &primary_commitment_key,
                &multi_circuit,
                17,
                &secondary_commitment_key,
                &ivc::step_circuit::trivial::Circuit::default(),
            );
            let primary_input = z_in;
            let secondary_input = array::from_fn(|i| bn256::Fq::from(i as u64));

            let mut ivc = sangria::IVC::new(
                &pp,
                &multi_circuit,
                primary_input,
                &ivc::step_circuit::trivial::Circuit::default(),
                secondary_input,
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
            ivc.verify(&pp).expect("Sangria IVC verification failed");
        }
        Mode::Cyclefold => {
            let mut pp = cyclefold::PublicParams::new(
                &multi_circuit,
                primary_commitment_key,
                secondary_commitment_key,
                20,
            )
            .expect("Failed to create Cyclefold public params");
            let primary_input = z_in;
            let mut ivc = cyclefold::IVC::new(&mut pp, &multi_circuit, primary_input)
                .expect("Failed to create Cyclefold IVC");
            for _ in 0..FOLD_STEP_COUNT {
                ivc = ivc
                    .next(&pp, &multi_circuit)
                    .expect("Cyclefold next step failed");
            }
            ivc.verify(&pp).expect("Cyclefold IVC verification failed");
        }
    }
}

/// Macro to generate a benchmark function for a given IVC mode and a specific constant gate count.
macro_rules! bench_ivc {
    ($group:expr, $mode:expr, $gates:expr) => {{
        let bench_name = format!("{:?}_gates_{}", $mode, $gates);
        $group.bench_function(&bench_name, |b| {
            b.iter(|| {
                run_ivc_with_gate_count::<$gates, { $gates * BASE_ARITY }>($mode);
            });
        });
    }};
}

/// The main benchmark function.
/// Separate sets of gate counts are used for Sangria and Cyclefold.
pub fn benchmark_ivc(c: &mut Criterion) {
    // For Sangria, use these gate counts.
    {
        let mut group = c.benchmark_group("Sangria_IVC");
        bench_ivc!(group, Mode::Sangria, 5);
        bench_ivc!(group, Mode::Sangria, 10);
        bench_ivc!(group, Mode::Sangria, 20);
        group.finish();
    }

    // For Cyclefold, use a different set of gate counts.
    {
        let mut group = c.benchmark_group("Cyclefold_IVC");
        bench_ivc!(group, Mode::Cyclefold, 6);
        bench_ivc!(group, Mode::Cyclefold, 12);
        bench_ivc!(group, Mode::Cyclefold, 24);
        bench_ivc!(group, Mode::Cyclefold, 48);
        group.finish();
    }
}

criterion_group!(benches, benchmark_ivc);
criterion_main!(benches);
