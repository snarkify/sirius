use std::num::NonZeroUsize;

use crate::{
    halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeFieldBits},
    main_gate::MainGateConfig,
    poseidon::{poseidon_circuit::PoseidonChip, PoseidonHash, ROTrait, Spec},
};

mod support_circuit;

mod sfc;

#[allow(clippy::upper_case_acronyms)]
pub mod incrementally_verifiable_computation;

pub use incrementally_verifiable_computation::{PublicParams, IVC};

pub const T: usize = 5;
pub const T_MAIN_GATE: usize = 5;

pub const RATE: usize = T - 1;
pub const R_F: usize = 10;
pub const R_P: usize = 10;

/// Safety: because 64 != 0
pub const DEFAULT_LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(64) };

/// Safety: because 10 != 0
pub const DEFAULT_LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(20) };

pub fn ro_const<F: PrimeFieldBits + FromUniformBytes<64>>() -> Spec<F, T, RATE> {
    Spec::<F, T, RATE>::new(R_F, R_P)
}

pub fn ro<F: PrimeFieldBits + FromUniformBytes<64>>() -> PoseidonHash<F, T, RATE> {
    PoseidonHash::<F, T, RATE>::new(ro_const())
}

pub fn ro_chip<F: PrimeFieldBits + FromUniformBytes<64>>(
    main_gate_config: MainGateConfig<T>,
) -> PoseidonChip<F, T, RATE> {
    PoseidonChip::new(main_gate_config, ro_const())
}
