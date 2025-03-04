/// # Sangria IVC Example
///
/// This example demonstrates how to use Sangria for Incrementally Verifiable Computation.
/// Sangria is an IVC scheme based on Nova's folding approach but adapted for the
/// more flexible PLONKish arithmetization, supporting custom gates and lookup arguments.
///
/// ## Architecture Overview
/// Sangria uses a two-circuit architecture:
/// - **Primary Circuit**: Performs the actual computation steps (z_i → z_{i+1})
/// - **Secondary Circuit**: Handles cryptographic operations needed for folding
///
/// ## IVC Flow
/// 1. Initialize with a starting state z_0
/// 2. For each step i:
///    - Apply the step function F to get z_i = F(z_{i-1}, w_i)
///    - Fold this step into the accumulator
///    - Create a proof that can be verified
/// 3. The final result includes the final state z_n and a proof of correct computation
use std::{array, env};

use sirius::{
    commitment::CommitmentKey,
    ivc::{step_circuit::trivial, SangriaIVC},
    sangria_prelude::bn256::{new_default_pp, C1Affine, C1Scalar, C2Affine, C2Scalar},
};
use tracing::info_span;
use tracing_subscriber::{filter::LevelFilter, fmt::format::FmtSpan, EnvFilter};

/// Primary circuit arity: Number of inputs/outputs for the main computation circuit
/// For this trivial example, we're using 5 state elements
const PRIMARY_CIRCUIT_ARITY: usize = 5;

/// Secondary circuit arity: Number of inputs/outputs for the helper circuit
/// For the trivial example, we only need 1 state element
const SECONDARY_CIRCUIT_ARITY: usize = 1;

/// Minimum table size required for the primary circuit
///
/// This value must be at least 17 for internal operations.
/// For more complex circuits, increase this constant based on the number
/// and complexity of constraints.
const PRIMARY_CIRCUIT_TABLE_SIZE: usize = 17;

/// Commitment key size for the primary circuit
/// Controls the polynomial degree supported for commitments on the primary curve (bn256)
const PRIMARY_COMMITMENT_KEY_SIZE: usize = 21;

/// Minimum table size required for the secondary circuit
///
/// This value must be at least 17 for internal operations.
/// The secondary circuit typically handles cryptographic operations for the folding scheme.
const SECONDARY_CIRCUIT_TABLE_SIZE: usize = 17;

/// Commitment key size for the secondary circuit
/// Controls the polynomial degree supported for commitments on the secondary curve (grumpkin)
const SECONDARY_COMMITMENT_KEY_SIZE: usize = 21;

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

    // Step 1: Create the step circuits
    // In Sangria, we need both primary and secondary circuits
    // The primary circuit operates on the bn256 curve with 5 state elements
    let primary_circuit = trivial::Circuit::<PRIMARY_CIRCUIT_ARITY, C1Scalar>::default();
    // The secondary circuit operates on the grumpkin curve with 1 state element
    let secondary_circuit = trivial::Circuit::<SECONDARY_CIRCUIT_ARITY, C2Scalar>::default();

    // Step 2: Set up the commitment keys for polynomial commitments on both curves
    let primary_key = CommitmentKey::<C1Affine>::setup(PRIMARY_COMMITMENT_KEY_SIZE, b"bn256");
    let secondary_key =
        CommitmentKey::<C2Affine>::setup(SECONDARY_COMMITMENT_KEY_SIZE, b"grumpkin");

    // Step 3: Create the public parameters that define the Sangria IVC instance
    // These parameters combine circuit configurations, commitment keys, and table sizes
    let public_params = new_default_pp::<PRIMARY_CIRCUIT_ARITY, _, SECONDARY_CIRCUIT_ARITY, _>(
        SECONDARY_CIRCUIT_TABLE_SIZE as u32,
        &primary_key,
        &primary_circuit,
        PRIMARY_CIRCUIT_TABLE_SIZE as u32,
        &secondary_key,
        &secondary_circuit,
    );

    // Create a tracing span for performance monitoring
    let _s = info_span!("sangria_trivial").entered();

    // Step 4: Initialize the IVC with starting state values
    // - For primary circuit: [0, 1, 2, 3, 4]
    // - For secondary circuit: [0]
    let mut ivc = SangriaIVC::new(
        &public_params,
        &primary_circuit,
        array::from_fn(|i| C1Scalar::from(i as u64)), // Primary circuit initial state z_0
        &secondary_circuit,
        array::from_fn(|i| C2Scalar::from(i as u64)), // Secondary circuit initial state
        true,                                         // Enable debug mode for detailed logging
    )
    .unwrap();

    // Step 5: Execute a single fold step
    // This applies the step function F to transition from z_0 to z_1
    // For the trivial circuit, F is the identity function (output = input)
    ivc.fold_step(&public_params, &primary_circuit, &secondary_circuit)
        .unwrap();

    // Step 6: Verify the computation result
    // This checks that the proof is valid and the computation was performed correctly
    ivc.verify(&public_params).unwrap();

    // Note: In a real application with multiple steps, you would typically:
    //
    // 1. Create new circuit instances for each step with different private witness data
    //    - Private witness is the non-public data used in the computation
    //    - Each step can use different private inputs while maintaining the public state
    //
    // For example, as seen in the CLI example (examples/cli.rs):
    //
    // ```
    // // Create circuit instances with private inputs for each step
    // let primary_circuit = MyCircuit::new_with_private_data(...);
    // let secondary_circuit = MySecondaryCircuit::new_with_private_data(...);
    //
    // // Initialize IVC with initial state
    // let mut ivc = SangriaIVC::new(&pp, &primary_circuit, initial_state, ...);
    //
    // // For each step, you can use different private inputs by updating the circuits
    // for step in 1..total_steps {
    //     // Update circuits with new private witness data for this step
    //     primary_circuit.update_between_step();    // Changes private witness inside the circuit
    //     secondary_circuit.update_between_step();  // Changes private witness inside the circuit
    //
    //     // Execute the fold step with updated circuit instances (same circuit type but different private data)
    //     ivc.fold_step(&pp, &primary_circuit, &secondary_circuit);
    // }
    // ```
    //
    // The key insight is that between steps:
    // - The public state (z_i) flows through the computation chain
    // - The private witness (w_i) can change at each step
    // - This allows proving statements that involve multiple different private inputs
    //   while maintaining a consistent public state transition
}
