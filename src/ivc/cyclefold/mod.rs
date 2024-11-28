use std::num::NonZeroUsize;

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

/// Safety: because 32 != 0
pub const DEFAULT_LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(32) };

/// Safety: because 10 != 0
pub const DEFAULT_LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

pub fn ro_const<F: PrimeFieldBits + FromUniformBytes<64>>() -> Spec<F, T, RATE> {
    Spec::<F, T, RATE>::new(R_F, R_P)
}

pub fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
    PoseidonHash::<F, T, RATE>::new(ro_const())
}
