#![allow(clippy::type_complexity)]
#![allow(dead_code)] // TODO: remove it later
#![allow(non_snake_case)] // UPPER_CASE is used for ease of compatibility with Nova documentation

pub mod commitment;
pub mod constants;
pub mod gadgets;
pub mod main_gate;
pub mod nifs;
pub mod plonk;
pub mod polynomial;
pub mod poseidon;
pub mod util;

pub mod error;
