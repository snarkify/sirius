use crate::main_gate::{AssignedBit, RegionCtx, WrapValue};
use ff::{FromUniformBytes, PrimeFieldBits};
use halo2_proofs::{arithmetic::CurveAffine, plonk::Error};

pub mod poseidon_circuit;
pub mod poseidon_hash;
pub use poseidon_hash::PoseidonHash;

/// A helper trait to obsorb different objects into RO
pub trait AbsorbInRO<C: CurveAffine, RO: ROTrait<C>> {
    /// Absorbs the value in the provided RO
    fn absorb_into(&self, ro: &mut RO);
}

/// A helper trait that defines the constants associated with a hash function
pub trait ROConstantsTrait: Clone {
    /// produces constants/parameters associated with the hash function
    fn new(r_f: usize, r_p: usize) -> Self;
}

pub trait ROTrait<C: CurveAffine> {
    /// A type representing constants/parameters associated with the hash function
    type Constants: ROConstantsTrait;

    /// Initializes the hash function
    fn new(constants: Self::Constants) -> Self;

    /// Adds a base to the internal state
    fn absorb_base(&mut self, base: C::Base);

    /// Adds a point to the internal state
    fn absorb_point(&mut self, p: C);

    /// Returns a challenge by hashing the internal state
    fn squeeze(&mut self, num_bits: usize) -> C::Scalar;
}

/// A helper trait that defines the behavior of a hash function that we use as an RO in the circuit model
pub trait ROCircuitTrait<F: PrimeFieldBits + FromUniformBytes<64>> {
    /// Adds a scalar to the internal state
    fn absorb_base(&mut self, base: WrapValue<F>);

    /// Adds a point to the internal state
    fn absorb_point(&mut self, x: WrapValue<F>, y: WrapValue<F>);

    /// Returns a challenge of `num_bits` by hashing the internal state
    fn squeeze_n_bits(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        num_bits: usize,
    ) -> Result<Vec<AssignedBit<F>>, Error>;
}
