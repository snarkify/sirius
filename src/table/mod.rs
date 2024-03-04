//! This module implements the core functionalities to (1) obtain all necessary information from halo2
//! circuits and (2) run special soundness protocols.
//! It centers around the `TableData` struct, which encapsulates the PLONK constraint system and
//! handles the construction and operation of various PLONK components. Key features include:
//!
//! - Preparation and assembly of the constraint system
//! - Implementation of special soundness protocols (`run_sps_protocol_*` functions), essential for
//!   generating instance/witnesses/challenges securely
//! - Construction of permutation matrices, ensuring copy constraints consistency in the constraint system.
//! - Construction of lookup Arguments when the circuits contains lookup argument
//!
//! The module is the intermediate data representation of plonkish constrain system defined by the
//! circuits

mod circuit_data;
mod circuit_runner;
mod constraint_system_metainfo;
mod witness_data;

pub use circuit_runner::CircuitRunner;
pub(crate) use constraint_system_metainfo::ConstraintSystemMetainfo;
pub(crate) use witness_data::WitnessCollector;

#[cfg(test)]
mod new_tests;
