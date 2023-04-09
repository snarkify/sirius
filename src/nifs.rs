#![allow(non_snake_case)]

use std::io;
use halo2_proofs::arithmetic::CurveAffine;
use crate::commitment::CommitmentKey;
use crate::plonk::{PlonkStructure, RelaxedPlonkInstance, RelaxedPlonkWitness, PlonkInstance, PlonkWitness};
use crate::transcript::{Transcript, AbsorbInTranscript};
use std::marker::PhantomData;


#[derive(Clone, Debug)]
pub struct NIFS<C: CurveAffine, T:Transcript<C>>
{
  pub(crate) T_commitment: C,
  _marker: PhantomData<T>,
}


impl<C: CurveAffine, T:Transcript<C>> NIFS<C,T> {
    pub fn prove(
        ck: &CommitmentKey<C>, 
        transcript: &mut T,
        S: &PlonkStructure<C>,
        U1: &RelaxedPlonkInstance<C>,
        W1: &RelaxedPlonkWitness<C>,
        U2: &PlonkInstance<C>,
        W2: &PlonkWitness<C>,
    ) -> io::Result<()> { //-> Result<(NIFS<C,T>, (RelaxedPlonkInstance<C>, RelaxedPlonkWitness<C>))> {
        S.absorb_into(transcript)?;
        U1.absorb_into(transcript)?;
        U2.absorb_into(transcript)?;

        let (T, T_commitment) = S.commit_T(ck, S, U1, W1, U2, W2);
        transcript.common_point(T_commitment)?;
        let r = transcript.squeeze_challenge();
        Ok(())
    }

    pub fn verify(
        &self,
        transcript: T,
        U1: RelaxedPlonkInstance<C>,
        U2: PlonkInstance<C>,
        ) {
    }
}
