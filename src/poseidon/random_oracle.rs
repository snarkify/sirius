use std::{fmt, num::NonZeroUsize};

use ff::{FromUniformBytes, PrimeField, PrimeFieldBits};
use halo2_proofs::{arithmetic::CurveAffine, plonk::Error};

use crate::main_gate::{AssignedBit, RegionCtx, WrapValue};

/// A helper trait to obsorb different objects into RO
pub trait AbsorbInRO<F: PrimeField, RO: ROTrait<F>> {
    /// Absorbs the value in the provided RO
    fn absorb_into(&self, ro: &mut RO);
}

/// A helper trait that defines the constants associated with a hash function
pub trait ROConstantsTrait {
    /// produces constants/parameters associated with the hash function
    fn new(r_f: usize, r_p: usize) -> Self;
}

pub trait ROTrait<F: PrimeField> {
    /// A type representing constants/parameters associated with the hash function
    type Constants: ROConstantsTrait;

    /// Initializes the hash function
    fn new(constants: Self::Constants) -> Self;

    fn absorb(&mut self, value: &impl AbsorbInRO<F, Self>) -> &mut Self
    where
        Self: Sized,
    {
        value.absorb_into(self);
        self
    }

    /// Adds a base to the internal state
    fn absorb_field(&mut self, base: F) -> &mut Self;

    /// Adds a base to the internal state
    fn absorb_field_iter(&mut self, iter: impl Iterator<Item = F>) -> &mut Self {
        iter.for_each(|base| {
            self.absorb_field(base);
        });
        self
    }

    /// Adds a point to the internal state
    fn absorb_point<C: CurveAffine<Base = F>>(&mut self, p: &C) -> &mut Self;

    fn absorb_point_iter<'item, C: CurveAffine<Base = F>>(
        &mut self,
        points: impl Iterator<Item = &'item C>,
    ) -> &mut Self {
        points.for_each(|p| {
            self.absorb_point(p);
        });

        self
    }

    fn inspect(&self, scan: impl Fn(&[F]));

    /// Returns a challenge by hashing the internal state
    fn squeeze<C: CurveAffine<Base = F>>(&mut self, num_bits: NonZeroUsize) -> C::Scalar;
}

/// A helper trait that defines the behavior of a hash function used as a Random Oracle (RO)
/// within a circuit.
pub trait ROCircuitTrait<F: PrimeFieldBits + FromUniformBytes<64>> {
    /// Associated type represents the arguments required to initialize the hash function in the circuit.
    /// These could include various parameters like the number of rounds, the internal state size, etc.
    type Args: fmt::Debug + Clone;

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

    fn inspect(&self, scan: impl Fn(&[F]));

    /// Returns a challenge of `num_bits` by hashing the internal state
    fn squeeze_n_bits(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        num_bits: NonZeroUsize,
    ) -> Result<Vec<AssignedBit<F>>, Error>;
}

/// Random Oracle is represented as a pair of on-circuit & off-circuit types,
/// allowing the use of a single generic.
pub trait ROPair<F: PrimeField>
where
    F: ff::PrimeFieldBits + ff::FromUniformBytes<64>,
{
    /// Argument for creating on-circuit & off-circuit versions of oracles
    type Args: fmt::Debug + serde::Serialize + Clone;
    type Config;

    type OffCircuit: ROTrait<F, Constants = Self::Args>;
    type OnCircuit: ROCircuitTrait<F, Args = Self::Args, Config = Self::Config>;
}
