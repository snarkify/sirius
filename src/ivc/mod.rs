pub mod step_circuit;

pub mod step_folding_circuit;

mod fold_relaxed_plonk_instance_chip;
mod incrementally_verifiable_computation;
mod instance_computation;
mod public_params;

pub use halo2_proofs::circuit::SimpleFloorPlanner;
pub use incrementally_verifiable_computation::*;
pub use public_params::{CircuitPublicParamsInput, PublicParams};

pub const NUM_IO: usize = 2;
