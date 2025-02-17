pub mod consistency_markers_computation;
pub mod fold_relaxed_plonk_instance_chip;
pub mod incrementally_verifiable_computation;
pub mod instances_accumulator_computation;
pub mod public_params;
pub mod step_folding_circuit;

pub use incrementally_verifiable_computation::IVC;
pub use public_params::{CircuitPublicParamsInput, PublicParams};
