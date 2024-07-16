pub mod poseidon_circuit;
pub mod poseidon_hash;
pub mod random_oracle;
mod spec;

pub use poseidon_hash::PoseidonHash;
pub use random_oracle::*;
pub use spec::Spec;

use crate::ff::{FromUniformBytes, PrimeField, PrimeFieldBits};

pub struct PoseidonRO<const T: usize, const RATE: usize>;

impl<const T: usize, const RATE: usize, F: serde::Serialize + PrimeField> ROPair<F>
    for PoseidonRO<T, RATE>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    type Args = Spec<F, T, RATE>;
    type Config = crate::main_gate::MainGateConfig<T>;

    type OnCircuit = poseidon_circuit::PoseidonChip<F, T, RATE>;
    type OffCircuit = poseidon_hash::PoseidonHash<F, T, RATE>;
}
