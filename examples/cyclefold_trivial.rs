/// # Cyclefold IVC Example
///
/// This example demonstrates how to use Cyclefold for Incrementally Verifiable Computation.
/// Cyclefold represents a significant advancement in folding scheme evolution with better
/// performance for recursive proof composition.
///
/// ## Architecture Overview
/// Cyclefold uses a co-processor architecture:
/// - Only ONE main circuit is needed for computation (unlike Sangria's two-circuit approach)
/// - Cryptographic operations are delegated to a compact "co-processor" circuit
/// - More efficient for recursive proof composition than traditional folding schemes
///
/// ## IVC Flow
/// 1. Initialize with a starting state z_0
/// 2. For each step i:
///    - Apply the step function F to get z_i = F(z_{i-1}, w_i)
///    - Produce a proof for the current step
///    - The step-by-step model allows verification at any point in the chain
use std::{array, env, path::Path};

use sirius::{
    commitment::CommitmentKey,
    cyclefold_prelude::{
        bn256::{C1Affine, C1Scalar, C2Affine},
        PublicParams, IVC,
    },
    ff::Field,
    ivc::step_circuit::trivial,
};
use tracing::info_span;
use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

/// Circuit arity: Number of inputs/outputs for the computation circuit
/// For this trivial example, we're using 5 state elements
const CIRCUIT_ARITY: usize = 5;

/// Commitment key size for the primary circuit
/// Controls the polynomial degree supported for commitments
/// Cyclefold typically needs larger keys than Sangria (23 vs 21)
const PRIMARY_COMMITMENT_KEY_SIZE: usize = 23;

/// Minimum table size required for the computation circuit
///
/// This value must be at least 17 for internal operations.
/// Cyclefold typically needs a larger minimum value (20 vs 17)
/// For more complex circuits, increase this constant as needed.
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 20;

/// Commitment key size for the secondary circuit (co-processor)
/// Controls the polynomial degree supported for commitments on the secondary curve
const SECONDARY_COMMITMENT_KEY_SIZE: usize = 23;

/// Cache folder for storing and retrieving commitment keys
/// Improves startup performance by avoiding regeneration
const FOLDER: &str = ".cache/examples";

fn main() {
    // Set up tracing for performance monitoring
    let builder = tracing_subscriber::fmt()
        // Track span entry and exit events for time profiling
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        // Set default log level to DEBUG
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::DEBUG.into())
                .from_env_lossy(),
        );

    // Use JSON formatting for logs if the --json flag is provided
    // JSON logs are needed for structured time profiling
    if env::args().any(|arg| arg.eq("--json")) {
        builder.json().init();
    } else {
        builder.init();
    }

    // Step 1: Create the step circuit - Cyclefold only needs one main circuit
    // The co-processor circuit for cryptographic operations is handled internally
    let circuit = trivial::Circuit::<CIRCUIT_ARITY, C1Scalar>::default();

    // Step 2: Set up commitment keys, using caching for better performance
    // Primary key is on the bn256 curve
    //
    // Safety: This call is safe as long as the cache files remain unmodified. For more detail,
    // refer to the safety documentation
    let primary_key = unsafe {
        CommitmentKey::<C1Affine>::load_or_setup_cache(
            Path::new(FOLDER),
            "bn256",
            PRIMARY_COMMITMENT_KEY_SIZE,
        )
        .unwrap()
    };

    // Secondary key is on the grumpkin curve (used by the co-processor)
    //
    // Safety: This call is safe as long as the cache files remain unmodified. For more detail,
    // refer to the safety documentation
    let secondary_key = unsafe {
        CommitmentKey::<C2Affine>::load_or_setup_cache(
            Path::new(FOLDER),
            "grumpkin",
            SECONDARY_COMMITMENT_KEY_SIZE,
        )
        .unwrap()
    };

    // Step 3: Create the public parameters for Cyclefold IVC
    // Note: Cyclefold PublicParams are mutable during initialization (unlike Sangria)
    let mut public_params = PublicParams::new(
        &circuit,
        primary_key,
        secondary_key,
        PRIMARY_CIRCUIT_TABLE_SIZE as u32,
    )
    .unwrap();

    // Create a tracing span for performance monitoring
    let _s = info_span!("cyclefold_trivial").entered();

    // Step 4: Initialize the IVC with all-zero starting state [0,0,0,0,0]
    let mut ivc = IVC::new(
        &mut public_params,
        &circuit,
        array::from_fn(|_| C1Scalar::ZERO), // Initial state z_0 = [0,0,0,0,0]
    )
    .expect("Failed to initialize IVC (step=0)");

    // Step 5: Execute a single computation step
    // This applies the step function F to transition from z_0 to z_1
    // For the trivial circuit, F is the identity function (output = input)
    ivc = ivc
        .next(&public_params, &circuit) // Compute z_1 = F(z_0, w_1)
        .expect("Failed to compute next step (step=1)");

    // Step 6: Verify the computation result
    // This checks that the proof is valid and the computation was performed correctly
    ivc.verify(&public_params)
        .expect("Failed to verify computation result");

    // Note: In a real application with multiple steps, you would typically:
    //
    // 1. Create new circuit instances for each step with different private witness data
    //    - Private witness is the non-public data used in the computation
    //    - Each step can use different private inputs while maintaining the public state
    //
    // For example, as seen in the CLI example (examples/cli.rs):
    //
    // ```
    // // Create circuit instance with private inputs
    // let circuit = MyCircuit::new_with_private_data(...);
    //
    // // Initialize IVC with initial state
    // let mut ivc = IVC::new(&mut public_params, &circuit, initial_state);
    //
    // // For each step, you can use different private inputs by updating the circuit
    // for step in 1..total_steps {
    //     // Update circuit with new private witness data for this step
    //     circuit.update_between_step();    // Changes private witness inside the circuit
    //
    //     // Execute the next step with the updated circuit (same circuit type but different private data)
    //     ivc = ivc.next(&public_params, &circuit);
    // }
    // ```
    //
    // The key insight is that between steps:
    // - The public state (z_i) flows through the computation chain
    // - The private witness (w_i) can change at each step
    // - This allows proving statements that involve multiple different private inputs
    //   while maintaining a consistent public state transition
}
