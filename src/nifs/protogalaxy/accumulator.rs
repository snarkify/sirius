use std::{iter, ops::Deref};

use crate::{
    ff::Field,
    halo2curves::CurveAffine,
    ivc::protogalaxy::verify_chip::BigUintPoint,
    plonk::{self, PlonkInstance, PlonkTrace, PlonkWitness},
    poseidon::{AbsorbInRO, ROTrait},
};

/// Represents an accumulator for folding multiple instances into a single instance,
/// following the accumulation schemes.
///
/// TODO#266 Docs
#[derive(Clone, Debug)]
pub struct Accumulator<C: CurveAffine> {
    /// `φ`: Represents the combined state of all instances & witnesses. It is a summary that
    /// captures the essential data and relationships from the instances being merged.
    pub(crate) trace: PlonkTrace<C>,

    /// `β`: A random value used in the folding process. It helps ensure the unique
    /// and secure combination of instances, preventing manipulation.
    pub(crate) betas: Box<[C::ScalarExt]>,

    /// `e`: an accumulated value that encapsulates the result of the folding operation. it serves
    /// as a concise representation of the correctness and properties of the folded instances.
    pub(crate) e: C::ScalarExt,
}

impl<C: CurveAffine> Deref for Accumulator<C> {
    type Target = PlonkTrace<C>;
    fn deref(&self) -> &Self::Target {
        &self.trace
    }
}

impl<C: CurveAffine, RO: ROTrait<C::ScalarExt>> AbsorbInRO<C::ScalarExt, RO> for Accumulator<C> {
    fn absorb_into(&self, ro: &mut RO) {
        AccumulatorInstance::from(self.clone()).absorb_into(ro);
    }
}

pub type AccumulatorArgs = plonk::PlonkTraceArgs;

impl<C: CurveAffine> Accumulator<C> {
    pub fn new(args: AccumulatorArgs, count_of_evaluation: usize) -> Self {
        Self {
            betas: vec![C::ScalarExt::ZERO; count_of_evaluation.ilog2() as usize]
                .into_boxed_slice(),
            e: C::ScalarExt::ZERO,
            trace: PlonkTrace::new(args),
        }
    }

    pub fn W_commitment_len(&self) -> usize {
        self.trace.u.W_commitments.len()
    }
}

/// Represents an accumulator for folding multiple instances into a single instance,
/// following the accumulation schemes.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AccumulatorInstance<C: CurveAffine> {
    /// `φ`: Represents the combined state of all instances. It is a summary that captures the
    /// essential data and relationships from the instances being merged.
    pub(crate) ins: PlonkInstance<C>,

    /// `β`: A random value used in the folding process. It helps ensure the unique
    /// and secure combination of instances, preventing manipulation.
    pub(crate) betas: Box<[C::ScalarExt]>,

    /// `e`: an accumulated value that encapsulates the result of the folding operation. it serves
    /// as a concise representation of the correctness and properties of the folded instances.
    pub(crate) e: C::ScalarExt,
}

impl<C: CurveAffine> AccumulatorInstance<C> {
    pub fn into_acc(self, w: PlonkWitness<C::Scalar>) -> Accumulator<C> {
        let Self { ins, betas, e } = self;
        Accumulator {
            trace: PlonkTrace { u: ins, w },
            betas,
            e,
        }
    }
}

impl<C: CurveAffine> From<Accumulator<C>> for AccumulatorInstance<C> {
    fn from(value: Accumulator<C>) -> Self {
        let Accumulator {
            betas,
            trace: PlonkTrace { u: ins, w: _ },
            e,
        } = value;

        AccumulatorInstance { betas, ins, e }
    }
}

impl<C: CurveAffine, RO: ROTrait<C::ScalarExt>> AbsorbInRO<C::ScalarExt, RO>
    for AccumulatorInstance<C>
{
    fn absorb_into(&self, ro: &mut RO) {
        let PlonkInstance {
            W_commitments,
            instances,
            challenges,
        } = &self.ins;

        ro.absorb_field_iter(
            W_commitments
                .iter()
                .flat_map(|W_commitment| {
                    let BigUintPoint { x, y } = BigUintPoint::new(W_commitment).unwrap();
                    x.into_iter().chain(y)
                })
                .chain(
                    instances
                        .iter()
                        .flat_map(|instance| instance.iter())
                        .copied(),
                )
                .chain(challenges.iter().copied())
                .chain(self.betas.iter().copied())
                .chain(iter::once(self.e))
                .map(|b| crate::util::fe_to_fe(&b).unwrap()),
        );
    }
}
