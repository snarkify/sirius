#![allow(non_snake_case)]
use crate::commitment::CommitmentKey;
use crate::constants::NUM_CHALLENGE_BITS;
use crate::polynomial::Expression;
use crate::poseidon::{AbsorbInRO, ROTrait};
use crate::table::{
    PlonkInstance, PlonkStructure, RelaxedPlonkInstance, RelaxedPlonkWitness, TableData,
};
use halo2_proofs::arithmetic::CurveAffine;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NIFS<C: CurveAffine, RO: ROTrait<C>> {
    pub(crate) cross_term_commits: Vec<C>,
    _marker: PhantomData<RO>,
}

impl<C: CurveAffine, RO: ROTrait<C>> NIFS<C, RO> {
    pub fn prove(
        &self,
        gates: &Vec<Expression<C::ScalarExt>>,
        ck: &CommitmentKey<C>,
        ro: &mut RO,
        td: &TableData<C::ScalarExt>,
        U1: &RelaxedPlonkInstance<C>,
        W1: &RelaxedPlonkWitness<C::ScalarExt>,
    ) -> (
        NIFS<C, RO>,
        (RelaxedPlonkInstance<C>, RelaxedPlonkWitness<C::ScalarExt>),
    ) {
        // TODO: hash gates into ro
        td.plonk_structure(ck).absorb_into(ro);
        let U2 = td.plonk_instance(ck);
        let W2 = td.plonk_witness();
        U1.absorb_into(ro);
        U2.absorb_into(ro);
        // TODO: add support for multiple gates
        let (cross_terms, cross_term_commits) = td.commit_cross_terms(&gates[0], ck);
        let _ = cross_term_commits
            .iter()
            .map(|cm| ro.absorb_point(*cm))
            .collect::<Vec<_>>();
        let r = ro.squeeze(NUM_CHALLENGE_BITS);
        let U = U1.fold(&U2, &cross_term_commits, &r);
        let W = W1.fold(&W2, &cross_terms, &r);
        (
            Self {
                cross_term_commits,
                _marker: PhantomData,
            },
            (U, W),
        )
    }

    pub fn verify(
        &self,
        ro: &mut RO,
        S: PlonkStructure<C>,
        U1: RelaxedPlonkInstance<C>,
        U2: PlonkInstance<C>,
    ) -> RelaxedPlonkInstance<C> {
        S.absorb_into(ro);
        U1.absorb_into(ro);
        U2.absorb_into(ro);
        let _ = self
            .cross_term_commits
            .iter()
            .map(|cm| ro.absorb_point(*cm))
            .collect::<Vec<_>>();
        let r = ro.squeeze(NUM_CHALLENGE_BITS);
        let U = U1.fold(&U2, &self.cross_term_commits, &r);
        U
    }
}
