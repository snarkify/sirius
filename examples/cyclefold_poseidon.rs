/// This module represents an implementation of `StepCircuit` based on the poseidon chip
pub mod poseidon_step_circuit {
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::{AssignedCell, Layouter},
        plonk::ConstraintSystem,
    };
    use sirius::{
        ff::{FromUniformBytes, PrimeFieldBits},
        ivc::{StepCircuit, SynthesisError},
        main_gate::{MainGate, MainGateConfig, RegionCtx, WrapValue},
        poseidon::{poseidon_circuit::PoseidonChip, Spec},
    };
    use tracing::*;

    /// Input and output size for `StepCircuit` within each step
    pub const ARITY: usize = 1;

    /// Spec for on-circuit poseidon circuit
    const POSEIDON_PERMUTATION_WIDTH: usize = 3;
    const POSEIDON_RATE: usize = POSEIDON_PERMUTATION_WIDTH - 1;

    pub type CircuitPoseidonSpec<F> = Spec<F, POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE>;

    const R_F1: usize = 4;
    const R_P1: usize = 3;

    #[derive(Clone, Debug)]
    pub struct TestPoseidonCircuitConfig {
        pconfig: MainGateConfig<POSEIDON_PERMUTATION_WIDTH>,
    }

    #[derive(Debug)]
    pub struct TestPoseidonCircuit<F: PrimeFieldBits> {
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
            let spec = CircuitPoseidonSpec::<F>::new(R_F1, R_P1);

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
}

use std::{array, env, io, path::Path};

use bn256::G1 as C1;
use grumpkin::G1 as C2;
use metadata::LevelFilter;
use sirius::{
    commitment::CommitmentKey,
    group::{prime::PrimeCurve, Group},
    halo2curves::{bn256, grumpkin, CurveAffine},
    ivc::cyclefold,
};
use tracing::*;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

/// `K` table size for primary circuit
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 21;

/// Разрмер commitment key
const COMMITMENT_KEY_SIZE: usize = 25;

type C1Affine = <C1 as PrimeCurve>::Affine;
type C1Scalar = <C1 as Group>::Scalar;

type C2Affine = <C2 as PrimeCurve>::Affine;

/// Either takes the key from [`CACHE_FOLDER`] or generates a new one and puts it in it
#[instrument]
pub fn get_or_create_commitment_key<C: CurveAffine>(
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

    let primary_commitment_key =
        get_or_create_commitment_key::<C1Affine>(COMMITMENT_KEY_SIZE, "bn256")
            .expect("Failed to get primary key");
    let secondary_commitment_key =
        get_or_create_commitment_key::<C2Affine>(COMMITMENT_KEY_SIZE, "grumpkin")
            .expect("Failed to get secondary key");

    let mut pp = cyclefold::PublicParams::new(
        &primary,
        primary_commitment_key,
        secondary_commitment_key,
        PRIMARY_CIRCUIT_TABLE_SIZE as u32,
    )
    .unwrap();

    let primary_input = array::from_fn(|i| C1Scalar::from(i as u64));

    let mut ivc = cyclefold::IVC::new(&mut pp, &primary, primary_input).expect("while step=0");

    for step in 1..=10 {
        ivc = ivc
            .next(&pp, &primary)
            .unwrap_or_else(|err| panic!("while step={step}: {err:?}"));
    }

    ivc.verify(&pp).expect("while verify");
}
