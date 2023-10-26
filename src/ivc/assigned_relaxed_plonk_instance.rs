use std::num::NonZeroUsize;

use ff::Field;
use halo2_proofs::{circuit::AssignedCell, plonk::ConstraintSystem};
use halo2curves::CurveAffine;

use crate::{
    gadgets::nonnative::bn::big_nat::BigNat,
    nifs::CrossTermCommits,
    plonk::RelaxedPlonkInstance,
    poseidon::{AbsorbInRO, ROTrait},
};

use super::SynthesisError;

/// `AssignedPoint` provides an elliptic curve abstraction inside a circuit.
#[derive(Clone)]
pub(crate) struct AssignedPoint<F: Field> {
    pub x: AssignedCell<F, F>,
    pub y: AssignedCell<F, F>,
    pub is_infinity: AssignedCell<F, F>,
}

/// An Allocated Relaxed R1CS Instance
pub(crate) struct AssignedRelaxedPlonkInstance<C: CurveAffine> {
    pub W: AssignedPoint<C::Base>,
    pub E: AssignedPoint<C::Base>,
    pub u: AssignedCell<C::Base, C::Base>,

    pub X0: BigNat<C::Scalar>,
    pub X1: BigNat<C::Scalar>,
}

impl<RO: ROTrait<C>, C: CurveAffine> AbsorbInRO<C, RO> for AssignedRelaxedPlonkInstance<C> {
    fn absorb_into(&self, _ro: &mut RO) {
        todo!()
    }
}

impl<C: CurveAffine> AssignedRelaxedPlonkInstance<C> {
    pub fn new(
        _cs: &mut ConstraintSystem<C::Base>,
        _instance: &RelaxedPlonkInstance<C>,
        _limb_width: NonZeroUsize,
        _n_limbs: NonZeroUsize,
    ) -> Self {
        todo!()
    }

    pub fn fold(
        &self,
        _cs: &mut ConstraintSystem<C::Base>,
        _public_params_commit: &C::Base,
        _instance: &RelaxedPlonkInstance<C>,
        _cross_term_commits: &CrossTermCommits<C>,
    ) -> Result<Self, SynthesisError> {
        todo!()
    }
}
