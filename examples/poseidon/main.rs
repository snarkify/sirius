/// This module represents an implementation of `StepCircuit` based on the poseidon chip
mod poseidon_step_circuit {
    use std::marker::PhantomData;

    use ff::{FromUniformBytes, PrimeFieldBits};

    use halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::ConstraintSystem,
    };
    use sirius::{
        ivc::{StepCircuit, SynthesisError},
        main_gate::{MainGate, MainGateConfig, RegionCtx, WrapValue},
        poseidon::{poseidon_circuit::PoseidonChip, Spec},
    };

    /// Input and output size for `StepCircuit` within each step
    pub const ARITY: usize = 1;

    /// Spec for on-circuit poseidon circuit
    const POSEIDON_PERMUTATION_WIDTH: usize = 3;
    const POSEIDON_RATE: usize = POSEIDON_PERMUTATION_WIDTH - 1;

    type CircuitPoseidonSpec<F> = Spec<F, POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE>;

    const R_F1: usize = 4;
    const R_P1: usize = 3;

    #[derive(Clone, Debug)]
    pub struct TestPoseidonCircuitConfig {
        pconfig: MainGateConfig<POSEIDON_PERMUTATION_WIDTH>,
    }

    #[derive(Default, Debug)]
    pub struct TestPoseidonCircuit<F: PrimeFieldBits> {
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
            let spec = CircuitPoseidonSpec::<F>::new(R_F1, R_P1);
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
}

use std::{array, env, io, num::NonZeroUsize, path::Path};

use ff::PrimeField;

use halo2curves::{bn256, grumpkin, CurveAffine};

use metadata::LevelFilter;

use bn256::G1 as C1;
use grumpkin::G1 as C2;

use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit, CircuitPublicParamsInput, PublicParams, IVC},
    poseidon::{self, ROPair},
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

/// `K` table size for primary circuit
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 17;
/// `K` table size for secondary circuit
const SECONDARY_CIRCUIT_TABLE_SIZE: usize = 17;

/// Разрмер commitment key
const COMMITMENT_KEY_SIZE: usize = 21;

use poseidon_step_circuit::{TestPoseidonCircuit, ARITY};

/// Specification for the random oracle used within IVC
const MAIN_GATE_SIZE: usize = 5;
const RATE: usize = 4;

type RandomOracle = poseidon::PoseidonRO<MAIN_GATE_SIZE, RATE>;
type RandomOracleConstant<F> = <RandomOracle as ROPair<F>>::Args;

/// Inside the IVC, big-uint math is used, these parameters define width of one limb
const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };
/// Inside the IVC, big-uint math is used, these parameters define maximum count of limbs
const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

type C1Affine = <C1 as halo2curves::group::prime::PrimeCurve>::Affine;
type C1Scalar = <C1 as halo2curves::group::Group>::Scalar;

type C2Affine = <C2 as halo2curves::group::prime::PrimeCurve>::Affine;
type C2Scalar = <C2 as halo2curves::group::Group>::Scalar;

/// Either takes the key from [`CACHE_FOLDER`] or generates a new one and puts it in it
#[instrument]
fn get_or_create_commitment_key<C: CurveAffine>(
    k: usize,
    label: &'static str,
) -> io::Result<CommitmentKey<C>> {
    /// Relative directory where the generated `CommitmentKey` stored
    const CACHE_FOLDER: &str = ".cache/examples";

    // Safety: Safe if you have not manually modified the generated files in [`CACHE_FOLDER`]
    unsafe { CommitmentKey::load_or_setup_cache(Path::new(CACHE_FOLDER), label, k) }
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

    // To osterize the total execution time of the example
    let _span = info_span!("poseidon_example").entered();

    let primary = poseidon_step_circuit::TestPoseidonCircuit::default();
    let secondary = step_circuit::trivial::Circuit::<ARITY, _>::default();

    // Specifications for random oracle used as part of the IVC algorithm
    let primary_spec = RandomOracleConstant::<C1Scalar>::new(10, 10);
    let secondary_spec = RandomOracleConstant::<C2Scalar>::new(10, 10);

    let primary_commitment_key =
        get_or_create_commitment_key::<C1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get primary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<C2Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get secondary key");

    let pp = PublicParams::<
        '_,
        ARITY,
        ARITY,
        MAIN_GATE_SIZE,
        C1Affine,
        C2Affine,
        TestPoseidonCircuit<_>,
        step_circuit::trivial::Circuit<ARITY, _>,
        RandomOracle,
        RandomOracle,
    >::new(
        CircuitPublicParamsInput::new(
            PRIMARY_CIRCUIT_TABLE_SIZE as u32,
            &primary_commitment_key,
            primary_spec,
            &primary,
        ),
        CircuitPublicParamsInput::new(
            SECONDARY_CIRCUIT_TABLE_SIZE as u32,
            &secondary_commitment_key,
            secondary_spec,
            &secondary,
        ),
        LIMB_WIDTH,
        LIMBS_COUNT,
    )
    .unwrap();

    let primary_input = array::from_fn(|i| C1Scalar::from_u128(i as u128));
    let secondary_input = array::from_fn(|i| C2Scalar::from_u128(i as u128));
    let fold_step_count = NonZeroUsize::new(10).unwrap();

    IVC::fold(
        &pp,
        primary,
        primary_input,
        secondary,
        secondary_input,
        fold_step_count,
    )
    .unwrap();
}
