#![allow(clippy::type_complexity)]
#![allow(dead_code)]
#![allow(non_snake_case)]

pub mod commitment;
pub mod constants;
pub mod gadgets;
pub mod main_gate;
pub mod nifs;
pub mod polynomial;
pub mod poseidon;
pub mod table;
pub mod util;

/// Wrapper for [`halo2_proofs::plonk::Error`] to
/// impl [`PartialEq`] & [`Eq`] and be able to use
/// it in [`assert_eq`] and other comparisons
#[derive(Debug)]
pub struct Halo2PlonkError(halo2_proofs::plonk::Error);

impl PartialEq for Halo2PlonkError {
    fn eq(&self, _other: &Self) -> bool {
        matches!(self, _other)
    }
}
impl Eq for Halo2PlonkError {}
impl From<halo2_proofs::plonk::Error> for Halo2PlonkError {
    fn from(value: halo2_proofs::plonk::Error) -> Self {
        Self(value)
    }
}
