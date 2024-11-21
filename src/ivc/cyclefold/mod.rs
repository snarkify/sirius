use halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeFieldBits};

use crate::poseidon::{PoseidonHash, ROTrait, Spec};

mod support_circuit;

mod sfc;

#[allow(clippy::upper_case_acronyms)]
mod incrementally_verifiable_computation;

pub const T: usize = 10;
pub const RATE: usize = T - 1;
pub const R_F: usize = 10;
pub const R_P: usize = 10;

pub fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
    PoseidonHash::<F, T, RATE>::new(Spec::<F, T, RATE>::new(R_F, R_P))
}
