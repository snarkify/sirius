use std::iter;

use crate::{
    ff::Field,
    halo2curves::CurveAffine,
    plonk::{RelaxedPlonkTrace, RelaxedPlonkTraceArgs},
    poseidon::{AbsorbInRO, ROTrait},
    util,
};

/// TODO#266 Docs
pub struct Accumulator<C: CurveAffine> {
    /// TODO#266 Docs
    pub(super) betas: Box<[C::ScalarExt]>,
    /// TODO#266 Docs
    pub(super) trace: RelaxedPlonkTrace<C>,
    /// TODO#266 Docs
    pub(super) e: C::ScalarExt,
}

impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO> for Accumulator<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb(&self.trace.U).absorb_field_iter(
            self.betas
                .iter()
                .chain(iter::once(&self.e))
                .map(|b| util::fe_to_fe::<C::ScalarExt, C::Base>(b).unwrap()),
        );
    }
}

pub type AccumulatorArgs = RelaxedPlonkTraceArgs;

impl<C: CurveAffine> Accumulator<C> {
    pub fn new(args: AccumulatorArgs, count_of_evaluation: usize) -> Self {
        Self {
            betas: vec![C::ScalarExt::ZERO; count_of_evaluation].into_boxed_slice(),
            e: C::ScalarExt::ZERO,
            trace: RelaxedPlonkTrace::new(args),
        }
    }

    pub fn fold(self, gamma: C::ScalarExt) -> Self {
        todo!("fold with {gamma:?}")
    }
}
