use crate::{
    gadgets::nonnative::bn::big_uint::BigUint,
    halo2_proofs::halo2curves::{ff::PrimeField, CurveAffine},
    nifs, plonk,
};

pub struct BigUintPoint<F: PrimeField> {
    x: BigUint<F>,
    y: BigUint<F>,
}

impl<C: CurveAffine> From<&C> for BigUintPoint<C::ScalarExt> {
    fn from(_value: &C) -> Self {
        todo!()
    }
}

pub struct PlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<BigUintPoint<F>>,
    pub(crate) instances: Vec<Vec<F>>,
    pub(crate) challenges: Vec<F>,
}

impl<C: CurveAffine> From<plonk::PlonkInstance<C>> for PlonkInstance<C::ScalarExt> {
    fn from(value: plonk::PlonkInstance<C>) -> Self {
        Self {
            W_commitments: value.W_commitments.iter().map(BigUintPoint::from).collect(),
            instances: value.instances,
            challenges: value.challenges,
        }
    }
}

pub struct AccumulatorInstance<F: PrimeField> {
    pub(crate) ins: PlonkInstance<F>,
    pub(crate) betas: Box<[F]>,
    pub(crate) e: F,
}

impl<C: CurveAffine> From<nifs::protogalaxy::AccumulatorInstance<C>>
    for AccumulatorInstance<C::ScalarExt>
{
    fn from(_value: nifs::protogalaxy::AccumulatorInstance<C>) -> Self {
        todo!()
    }
}

pub struct SelfTrace<F: PrimeField> {
    pub input_accumulator: AccumulatorInstance<F>,
    pub incoming: PlonkInstance<F>,
    pub output_accumulator: AccumulatorInstance<F>,
}

pub struct PairedTrace<C: CurveAffine> {
    pub input_accumulator: nifs::protogalaxy::AccumulatorInstance<C>,
    pub incoming: plonk::PlonkInstance<C>,
    pub output_accumulator: nifs::protogalaxy::AccumulatorInstance<C>,
}

pub struct Input<const ARITY: usize, C: CurveAffine> {
    pub pp_digest: (C::ScalarExt, C::ScalarExt),

    pub self_trace: SelfTrace<C::ScalarExt>,
    pub paired_trace: PairedTrace<C>,

    pub proof: nifs::protogalaxy::Proof<C::ScalarExt>,

    pub step: usize,
    pub z_0: [C::ScalarExt; ARITY],
    pub z_i: [C::ScalarExt; ARITY],
}

impl<const ARITY: usize, C: CurveAffine> Input<ARITY, C> {
    pub(super) fn without_witness(&self) -> Self {
        todo!()
    }
}
