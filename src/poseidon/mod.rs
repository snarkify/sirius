pub mod poseidon_circuit;
pub mod poseidon_hash;
pub mod random_oracle;
mod spec;

pub use poseidon_hash::PoseidonHash;
pub use random_oracle::*;
pub use spec::Spec;

pub struct PoseidonRO<const T: usize, const RATE: usize>;

impl<const T: usize, const RATE: usize, F: ff::PrimeField> ROPair<F> for PoseidonRO<T, RATE>
where
    F: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    type Args = Spec<F, T, RATE>;
    type OnCircuit = poseidon_circuit::PoseidonChip<F, T, RATE>;
    type OffCircuit = poseidon_hash::PoseidonHash<F, T, RATE>;
}
