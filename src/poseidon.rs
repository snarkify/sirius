use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::AssignedCell,
    plonk::Error,
};
use crate::main_gate::RegionCtx;

pub mod poseidon_hash;
pub mod poseidon_circuit;

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

  /// Adds a scalar to the internal state
  fn absorb_scalar(&mut self, scalar: C::Scalar);

  /// Adds a point to the internal state
  fn absorb_point(&mut self, point: C);

  /// Returns a challenge by hashing the internal state
  fn squeeze(&mut self) -> C::Scalar;
}

/// A helper trait that defines the behavior of a hash function that we use as an RO in the circuit model
pub trait ROCircuitTrait<C: CurveAffine> {
  /// A type representing constants/parameters associated with the hash function
  type Constants: ROConstantsTrait;

  /// Initializes the hash function
  fn new(constants: Self::Constants, num_absorbs: usize) -> Self;

  /// Adds a scalar to the internal state
  fn absorb_scalar(&mut self, scalar: AssignedCell<C::Scalar, C::Scalar>);

  /// Adds a point to the internal state
  fn absorb_point(&mut self, p: C);

  /// Returns a challenge of `num_bits` by hashing the internal state
  fn squeeze(&mut self, ctx: &mut RegionCtx<'_, C::Scalar>) -> Result<Vec<AssignedCell<C::Scalar, C::Scalar>>, Error>;
}


