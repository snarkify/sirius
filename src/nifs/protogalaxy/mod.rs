use std::marker::PhantomData;

use halo2_proofs::arithmetic::CurveAffine;

use super::*;
use crate::{
    commitment::CommitmentKey,
    ff::PrimeField,
    plonk::{PlonkStructure, PlonkTrace, RelaxedPlonkInstance, RelaxedPlonkTrace},
};

pub(crate) mod poly;

/// ProtoGalaxy: Non Interactive Folding Scheme that implements main protocol defined in paper
/// [protogalaxy](https://eprint.iacr.org/2023/1106)
#[derive(Clone, Debug)]
pub struct ProtoGalaxy<C: CurveAffine> {
    _marker: PhantomData<C>,
}

pub struct ProtoGalaxyProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// digest of public parameter of IVC circuit
    pp_digest: C,
}

pub struct ProtoGalaxyProof<F: PrimeField> {
    // TODO: add comments
    pub poly_F: Vec<F>,
    pub poly_K: Vec<F>,
}

impl<C: CurveAffine, const L: usize> FoldingScheme<C, L> for ProtoGalaxy<C> {
    type ProverParam = ProtoGalaxyProverParam<C>;
    type VerifierParam = C;
    type Accumulator = RelaxedPlonkTrace<C>;
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
