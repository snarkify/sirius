use std::{iter, marker::PhantomData};

use halo2_proofs::arithmetic::{CurveAffine, Field};
use tracing::instrument;

use super::*;
use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    ff::PrimeField,
    plonk::{PlonkStructure, PlonkTrace, RelaxedPlonkInstance},
    polynomial::univariate::UnivariatePoly,
    sps,
};

mod accumulator;
pub(crate) mod poly;

pub use accumulator::{Accumulator, AccumulatorArgs};

/// ProtoGalaxy: Non Interactive Folding Scheme that implements main protocol defined in paper
/// [protogalaxy](https://eprint.iacr.org/2023/1106)
#[derive(Clone, Debug)]
pub struct ProtoGalaxy<C: CurveAffine> {
    _marker: PhantomData<C>,
}

impl<C: CurveAffine> ProtoGalaxy<C> {
    #[instrument(skip_all)]
    pub(crate) fn generate_challenge<'i>(
        pp_digest: &C,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Accumulator<C>,
        instances: impl Iterator<Item = &'i PlonkInstance<C>>,
    ) -> <C as CurveAffine>::ScalarExt {
        ro_acc
            .absorb_point(pp_digest)
            .absorb(accumulator)
            .absorb_iter(instances)
            .squeeze::<C>(NUM_CHALLENGE_BITS)
    }

    fn get_count_of_valuation(S: &PlonkStructure<C::ScalarExt>) -> usize {
        let count_of_rows = 2usize.pow(S.k as u32);
        let count_of_gates = S.gates.len();

        count_of_rows * count_of_gates
    }

    pub(crate) fn new_accumulator(
        args: AccumulatorArgs,
        params: &ProtoGalaxyProverParam<C>,
        ro_acc: &mut impl ROTrait<C::Base>,
    ) -> Accumulator<C> {
        let mut accumulator = Accumulator::new(args, Self::get_count_of_valuation(&params.S));

        let beta = Self::generate_challenge(&params.pp_digest, ro_acc, &accumulator, iter::empty());

        accumulator
            .betas
            .iter_mut()
            .zip(iter::successors(Some(beta), |acc| Some(acc.double())))
            .for_each(|(b, beta_pow)| *b = beta_pow);

        accumulator
    }
}

pub struct ProtoGalaxyProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// digest of public parameter of IVC circuit
    pp_digest: C,
}

pub struct ProtoGalaxyProof<F: PrimeField> {
    pub poly_F: UnivariatePoly<F>,
    pub poly_K: UnivariatePoly<F>,
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Sps(#[from] sps::Error),
    #[error(transparent)]
    Poly(#[from] poly::Error),
}

impl<C: CurveAffine, const L: usize> FoldingScheme<C, L> for ProtoGalaxy<C> {
    type Error = Error;
    type ProverParam = ProtoGalaxyProverParam<C>;
    type VerifierParam = C;
    type Accumulator = Accumulator<C>;
    type AccumulatorInstance = RelaxedPlonkInstance<C>;
    type Proof = ProtoGalaxyProof<C::ScalarExt>;

    fn setup_params(
        pp_digest: C,
        S: PlonkStructure<C::ScalarExt>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        Ok((ProtoGalaxyProverParam { S, pp_digest }, pp_digest))
    }

    // TODO: if this function turned out to be the same, consider move to trait
    fn generate_plonk_trace(
        ck: &CommitmentKey<C>,
        instance: &[C::ScalarExt],
        witness: &[Vec<C::ScalarExt>],
        pp: &Self::ProverParam,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<PlonkTrace<C>, Error> {
        Ok(pp
            .S
            .run_sps_protocol(ck, instance, witness, ro_nark, pp.S.num_challenges)?)
    }

    fn prove(
        _ck: &CommitmentKey<C>,
        _pp: &Self::ProverParam,
        _ro_acc: &mut impl ROTrait<C::Base>,
        _accumulator: &Self::Accumulator,
        _incoming: &[PlonkTrace<C>; L],
    ) -> Result<(Self::Accumulator, Self::Proof), Error> {
        todo!()
    }

    fn verify(
        _vp: &Self::VerifierParam,
        _ro_nark: &mut impl ROTrait<C::Base>,
        _ro_acc: &mut impl ROTrait<C::Base>,
        _accumulator: &Self::AccumulatorInstance,
        _incoming: &[PlonkInstance<C>; L],
        _proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Error> {
        todo!()
    }
}
