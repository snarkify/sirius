use std::num::NonZeroUsize;

use crate::main_gate::{AssignedBit, RegionCtx, WrapValue};
use ff::{FromUniformBytes, PrimeFieldBits};
use halo2_proofs::{arithmetic::CurveAffine, plonk::Error};

pub mod poseidon_circuit;
pub mod poseidon_hash;
use poseidon::Spec;
pub use poseidon_hash::PoseidonHash;

/// A helper trait to obsorb different objects into RO
pub trait AbsorbInRO<C: CurveAffine, RO: ROTrait<C>> {
    /// Absorbs the value in the provided RO
    fn absorb_into(&self, ro: &mut RO);
}

/// A helper trait that defines the constants associated with a hash function
pub trait ROConstantsTrait {
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
    fn absorb_point(&mut self, p: &C);

    /// Returns a challenge by hashing the internal state
    fn squeeze(&mut self, num_bits: NonZeroUsize) -> C::Scalar;
}

/// A helper trait that defines the behavior of a hash function used as a Random Oracle (RO)
/// within a circuit.
pub trait ROCircuitTrait<F: PrimeFieldBits + FromUniformBytes<64>> {
    /// Associated type represents the arguments required to initialize the hash function in the circuit.
    /// These could include various parameters like the number of rounds, the internal state size, etc.
    type Args: Clone;

    /// Associated type represents the configuration settings for the hash function within the circuit.
    ///
    /// This includes defining the layout of gates, wires, and other circuit-specific parameters necessary for
    /// the hash function's operation within the proof system.
    type Config;

    /// Constructs a new instance of the random oracle circuit
    fn new(config: Self::Config, args: Self::Args) -> Self;

    /// Adds a scalar to the internal state
    fn absorb_base(&mut self, base: WrapValue<F>) -> &mut Self;

    /// Adds a point to the internal state
    fn absorb_point(&mut self, point: [WrapValue<F>; 2]) -> &mut Self;

    /// Adds elements of iterator of [`WrapValues`] to the internal state
    fn absorb_iter<I>(&mut self, iter: impl Iterator<Item = I>) -> &mut Self
    where
        I: Into<WrapValue<F>>,
    {
        iter.for_each(|val| {
            self.absorb_base(val.into());
        });
        self
    }

    /// Returns a challenge of `num_bits` by hashing the internal state
    fn squeeze_n_bits(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        num_bits: NonZeroUsize,
    ) -> Result<Vec<AssignedBit<F>>, Error>;
}

/// Random Oracle is represented as a pair of on-circuit & off-circuit types,
/// allowing the use of a single generic.
pub trait ROPair<C: CurveAffine>
where
    C::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    /// Argument for creating on-circuit & off-circuit versions of oracles
    type Args;

    type OffCircuit: ROTrait<C, Constants = Self::Args>;
    type OnCircuit: ROCircuitTrait<C::Base, Args = Self::Args>;
}

pub struct PoseidonRO<const T: usize, const RATE: usize>;

impl<const T: usize, const RATE: usize, C: CurveAffine> ROPair<C> for PoseidonRO<T, RATE>
where
    C::Base: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    type Args = Spec<C::Base, T, RATE>;
    type OnCircuit = poseidon_circuit::PoseidonChip<C::Base, T, RATE>;
    type OffCircuit = poseidon_hash::PoseidonHash<C, T, RATE>;
}
