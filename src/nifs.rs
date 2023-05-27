#![allow(non_snake_case)]
use halo2_proofs::arithmetic::CurveAffine;
use crate::commitment::CommitmentKey;
use crate::table::{PlonkStructure, RelaxedPlonkInstance, RelaxedPlonkWitness, PlonkInstance, PlonkWitness};
use crate::poseidon::{ROTrait, AbsorbInRO};
use std::marker::PhantomData;


#[derive(Clone, Debug)]
pub struct NIFS<C: CurveAffine, RO: ROTrait<C>>
{
  pub(crate) T_commitment: C,
  _marker: PhantomData<RO>,
}


impl<C: CurveAffine, RO:ROTrait<C>> NIFS<C, RO> {
    pub fn prove(
        ck: &CommitmentKey<C>, 
        ro: &mut RO,
        S: &PlonkStructure<C>,
        U1: &RelaxedPlonkInstance<C>,
        W1: &RelaxedPlonkWitness<C>,
        U2: &PlonkInstance<C>,
        W2: &PlonkWitness<C>,
    )  { //-> Result<(NIFS<C,T>, (RelaxedPlonkInstance<C>, RelaxedPlonkWitness<C>))> {
        S.absorb_into(ro);
        U1.absorb_into(ro);
        U2.absorb_into(ro);

//        let (T, T_commitment) = S.commit_T(ck, S, U1, W1, U2, W2);
//        transcript.common_point(T_commitment)?;
//        let r = transcript.squeeze_challenge();
    }

    pub fn verify(
        &self,
        ro: RO,
        U1: RelaxedPlonkInstance<C>,
        U2: PlonkInstance<C>,
        ) {
    }
}
