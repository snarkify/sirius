#![allow(non_snake_case)]

use std::io;
use group::Curve;
use halo2_proofs::arithmetic::CurveAffine;
use crate::commitment::CommitmentKey;
use crate::transcript::{Transcript, AbsorbInTranscript};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkStructure<C: CurveAffine> {
    pub(crate) fixed_columns: Vec<Vec<C::Scalar>>,
    pub(crate) fixed_commitments: Vec<C>,
}

#[derive(Clone, Debug)]
pub struct PlonkInstance<C: CurveAffine> {
    pub(crate) advice_commitments: Vec<C>,
    pub(crate) instance_commitments: Vec<C>,
    pub(crate) X: Vec<C>,
}


#[derive(Clone, Debug)]
pub struct PlonkWitness<C:CurveAffine> {
    pub(crate) advice_columns: Vec<Vec<C::Scalar>>,
    pub(crate) instance_columns: Vec<Vec<C::Scalar>>,
}

// [comm(a), comm(b), comm(c), comm(E), comm(inst), u, X]
// for standard_gate
#[derive(Clone, Debug)]
pub struct RelaxedPlonkInstance<C:CurveAffine> {
    pub(crate) advice_commitments: Vec<C>,
    pub(crate) instance_commitments: Vec<C>,
    pub(crate) E_commitment: C,
    pub(crate) u: C::Scalar,
    pub(crate) X: Vec<C>
}

// [a,b,c,e,inst] for standard_gate
#[derive(Clone, Debug)]
pub struct RelaxedPlonkWitness<C:CurveAffine> {
    pub(crate) advice_columns: Vec<Vec<C::Scalar>>,
    pub(crate) instance_columns: Vec<Vec<C::Scalar>>,
    pub(crate) E: Vec<C::Scalar>,
}

impl<C:CurveAffine> PlonkStructure<C> {
    /// A method to compute a commitment to the cross-term `T` given a
    /// Relaxed R1CS instance-witness pair and an R1CS instance-witness pair
    pub fn commit_T(
      &self,
      ck: &CommitmentKey<C>,
      S: &PlonkStructure<C>,
      U1: &RelaxedPlonkInstance<C>,
      W1: &RelaxedPlonkWitness<C>,
      U2: &PlonkInstance<C>,
      W2: &PlonkWitness<C>,
    ) -> (Vec<C::Scalar>, C) {
        // TODO: make it systematically for general expression
        assert!(S.fixed_columns.len() == 5);
        assert!(W1.advice_columns.len() == 3);
        let sa = S.fixed_columns[0].clone();
        let sb = S.fixed_columns[1].clone();
        let sc = S.fixed_columns[2].clone();
        let s_mul = S.fixed_columns[3].clone();
        let s_const = S.fixed_columns[4].clone();
        let a1 = W1.advice_columns[0].clone();
        let b1 = W1.advice_columns[1].clone();
        let c1 = W1.advice_columns[2].clone();
        let a2 = W2.advice_columns[0].clone();
        let b2 = W2.advice_columns[1].clone();
        let c2 = W2.advice_columns[2].clone();
        let u1 = U1.u;

        let I1 = (0..a1.len())
        .into_iter()
        .map(|i| a1[i] * sa[i] + b1[i] * sb[i] + c1[i] * sc[i] )
        .collect::<Vec<C::Scalar>>();

        let I2 = (0..a2.len())
        .into_iter()
        .map(|i| u1 * (a2[i] * sa[i] + b2[i] * sb[i] + c2[i] * sc[i]) )
        .collect::<Vec<C::Scalar>>();

        let I3 = (0..a1.len())
         .into_iter()
         .map(|i| s_mul[i] * (a2[i] * b1[i] + a1[i] + b2[i]))
         .collect::<Vec<C::Scalar>>();

        let I4 = (0..s_const.len())
            .into_iter()
            .map(|i| (u1+u1)*s_const[i])
            .collect::<Vec<C::Scalar>>();
        
        let T = I1.iter()
            .zip(&I2)
            .zip(&I3)
            .zip(&I4)
            .map(|(((t1,t2),t3),t4)| *t1+*t2+*t3+*t4)
            .collect::<Vec<C::Scalar>>();

        let T_commitment =  ck.commit(&T);

        (T, T_commitment)
    }
}



impl<C: CurveAffine, T: Transcript<C>> AbsorbInTranscript<C,T> for PlonkStructure<C> {
    fn absorb_into(&self, transcript: &mut T) -> io::Result<()> {
        for point in &self.fixed_commitments {
            transcript.common_point(*point)?;
        }
        Ok(())
    }
}

impl<C: CurveAffine, T: Transcript<C>> AbsorbInTranscript<C,T> for PlonkInstance<C> {
    fn absorb_into(&self, transcript: &mut T) -> io::Result<()> {
        for point in self.advice_commitments.iter().chain(self.instance_commitments.iter()).chain(self.X.iter()) {
            transcript.common_point(*point)?;
        }
        Ok(())
    }
}

impl<C:CurveAffine> RelaxedPlonkInstance<C> {
    pub fn fold(
        &self,
        U2: &PlonkInstance<C>,
        comm_T: &C,
        r: &C::Scalar,
    ) -> RelaxedPlonkInstance<C> {
      let (X1, u1, comms_adv1, comms_inst1, comm_E1) =
          (&self.X, &self.u, &self.advice_commitments, &self.advice_commitments, &self.E_commitment);
      let (X2, comms_adv2, comms_inst2) = (&U2.X, &U2.advice_commitments, &U2.instance_commitments);
      let X = X1
          .iter()
          .zip(X2)
          .map(|(a, b)| *a + b.mul(*r).to_affine())
          .map(|x| x.to_affine())
          .collect::<Vec<C>>();
      let comms_adv = comms_adv1 
          .iter()
          .zip(comms_adv2)
          .map(|(a, b)| *a + b.mul(*r).to_affine())
          .map(|x| x.to_affine())
          .collect::<Vec<C>>();
      let comms_inst = comms_inst1 
          .iter()
          .zip(comms_inst2)
          .map(|(a, b)| *a + b.mul(*r).to_affine())
          .map(|x| x.to_affine())
          .collect::<Vec<C>>();
      let comm_E = *comm_E1 - comm_T.mul(*r).to_affine();
      let u = *u1 + *r;

      RelaxedPlonkInstance {
          advice_commitments: comms_adv,
          instance_commitments: comms_inst,
          E_commitment: comm_E.to_affine(),
          u,
          X,
      }
    }
}

impl<C: CurveAffine, T: Transcript<C>> AbsorbInTranscript<C,T> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, transcript: &mut T) -> io::Result<()> {
        for point in self.advice_commitments.iter().chain(self.instance_commitments.iter()).chain(self.X.iter()) {
            transcript.common_point(*point)?;
        }
        transcript.common_scalar(self.u)?;
        transcript.common_point(self.E_commitment)?;
        Ok(())
    }
}

impl<C:CurveAffine> RelaxedPlonkWitness<C> {
    pub fn fold(
        &self,
        W2: &PlonkWitness<C>,
        T: &[C::Scalar],
        r: &C::Scalar,
    ) -> RelaxedPlonkWitness<C> {
        let (adv1, inst1, E1) = (&self.advice_columns, &self.advice_columns, &self.E);
        let (adv2, inst2) = (&W2.advice_columns, &W2.instance_columns);
        assert_eq!(adv1.len(), adv2.len());
        assert_eq!(adv1[0].len(), adv2[0].len());
        assert_eq!(inst1.len(), inst2.len());
        assert_eq!(inst1[0].len(), inst2[0].len());

        let fold_column = |(v1, v2): (&Vec<C::Scalar>, &Vec<C::Scalar>)| -> Vec<C::Scalar> {
            v1.iter()
                .zip(v2)
                .map(|(&a,&b)| a + b)
                .collect()
        };

        let adv =adv1 
           .iter()
           .zip(adv2)
           .map(fold_column)
           .collect::<Vec<_>>();

        let inst =inst1 
           .iter()
           .zip(inst2)
           .map(fold_column)
           .collect::<Vec<_>>();

        let E = E1
           .iter()
           .zip(T)
           .map(|(a, b)| *a - *r * *b)
           .collect::<Vec<C::Scalar>>();

        RelaxedPlonkWitness {
            advice_columns: adv,
            instance_columns: inst,
            E,
        }
    }
}

