//! This module defines the Plonk related types for working with
//! halo2 circuits. It provides functionality to retrieve PlonkStructure and witness
//! data, as well as defining various methods used by the folding scheme.
//!
//! The main types defined in this module are:
//! - PlonkStructure: Represents the structure of a Plonk circuit and its associated data.
//! - PlonkInstance: Represents an instance of a Plonk circuit.
//! - PlonkWitness: Represents the witness data for a Plonk circuit.
//! - RelaxedPlonkInstance: Represents an instance of a relaxed Plonk circuit.
//! - RelaxedPlonkWitness: Represents the witness data for a relaxed Plonk circuit.
//!
//! The module also provides implementations of the AbsorbInRO trait for
//! PlonkStructure, PlonkInstance, and RelaxedPlonkInstance.
//!
//! Additionally, it defines a method is_sat on PlonkStructure to determine if
//! a given Plonk instance and witness satisfy the circuit constraints.
use std::iter;

use ff::{Field, PrimeField};
use halo2_proofs::arithmetic::{best_multiexp, CurveAffine};
use itertools::Itertools;
use log::*;
use rayon::prelude::*;
use serde::Serialize;

use crate::{
    commitment::CommitmentKey,
    concat_vec,
    plonk::eval::{Error as EvalError, Eval, PlonkEvalDomain},
    polynomial::{
        sparse::{matrix_multiply, SparseMatrix},
        MultiPolynomial,
    },
    poseidon::{AbsorbInRO, ROTrait},
    sps::{Error as SpsError, SpecialSoundnessVerifier},
    util::fe_to_fe,
};

pub mod eval;
pub mod lookup;
pub mod permutation;
pub mod util;

#[derive(Debug, thiserror::Error, PartialEq)]
pub enum Error {
    #[error(transparent)]
    Sps(#[from] SpsError),
    #[error(transparent)]
    Eval(#[from] EvalError),
    #[error("(Relaxed) plonk relation not satisfied: commitment mismatch")]
    CommitmentMismatch,
    #[error("log derivative relation not satisfied")]
    LogDerivativeNotSat,
    #[error("Permutation check fail: mismatch_count {mismatch_count}")]
    PermCheckFail { mismatch_count: usize },
    #[error("(Relaxed) plonk relation not satisfied: mismatch_count {mismatch_count}, total_row {total_row}")]
    EvaluationMismatch {
        mismatch_count: usize,
        total_row: usize,
    },
}

#[derive(Clone, PartialEq, Serialize, Default)]
#[serde(bound(serialize = "
    F: Serialize
"))]
pub struct PlonkStructure<F: PrimeField> {
    /// k is a parameter such that 2^k is the total number of rows
    pub(crate) k: usize,
    pub(crate) selectors: Vec<Vec<bool>>,
    pub(crate) fixed_columns: Vec<Vec<F>>,

    pub(crate) num_advice_columns: usize,

    /// We follow the special soundness protocol(SPS), section 3.1 in [Protostar](https://eprint.iacr.org/2023/620)
    /// let k = num_challenges; when k > 0, we add extra verifier round, this is slightly different
    /// from protostar paper.
    /// see [`PlonkInstance::challenges`] for detail
    pub(crate) num_challenges: usize,
    /// specify the witness size of each prover round
    pub(crate) round_sizes: Vec<usize>,

    /// singla polynomial relation that combines custom gates and lookup relations
    pub(crate) poly: MultiPolynomial<F>,
    pub(crate) permutation_matrix: SparseMatrix<F>,
    pub(crate) lookup_arguments: Option<lookup::Arguments<F>>,
}

#[derive(Clone, Debug)]
pub struct PlonkInstance<C: CurveAffine> {
    /// `W_commitments = round_sizes.len()`, see [`PlonkStructure::round_sizes`]
    pub(crate) W_commitments: Vec<C>,
    /// inst = [X0, X1]
    pub(crate) instance: Vec<C::ScalarExt>,
    /// challenges generated in special soundness protocol
    /// we will have 0 ~ 3 challenges depending on different cases:
    /// name them as r1, r2, r3.
    /// r1: compress vector lookup, e.g. (a_1, a_2, a_3) -> a_1 + r1*a_2 + r1^2*a_3
    /// r2: challenge to calculate h and g in log-derivative relation
    /// r3: combine all custom gates (P_i) and lookup relations (L_i), e.g.:
    /// (P_1, P_2, L_1, L_2) -> P_1 + r3*P_2 + r3^2*L_1 + r3^3*L_2
    pub(crate) challenges: Vec<C::ScalarExt>,
}

impl<C: CurveAffine> Default for PlonkInstance<C> {
    fn default() -> Self {
        Self {
            W_commitments: vec![],
            instance: vec![C::ScalarExt::ZERO, C::ScalarExt::ZERO], // TODO Fix Me
            challenges: vec![],
        }
    }
}

#[derive(Clone, Debug)]
pub struct PlonkWitness<F: PrimeField> {
    /// length of W equals number of prover rounds, see [`PlonkStructure`]
    pub(crate) W: Vec<Vec<F>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelaxedPlonkInstance<C: CurveAffine> {
    pub(crate) W_commitments: Vec<C>,
    pub(crate) E_commitment: C,
    pub(crate) instance: Vec<C::ScalarExt>,
    /// contains challenges
    pub(crate) challenges: Vec<C::ScalarExt>,
    /// homogenous variable u
    pub(crate) u: C::ScalarExt,
}

#[derive(Clone, Debug)]
pub struct RelaxedPlonkWitness<F: PrimeField> {
    /// each vector element in W is a vector folded from an old [`RelaxedPlonkWitness.W`] and [`PlonkWitness.W`]
    pub(crate) W: Vec<Vec<F>>,
    pub(crate) E: Vec<F>,
}

// TODO #31 docs
pub struct RelaxedPlonkTrace<C: CurveAffine> {
    pub U: RelaxedPlonkInstance<C>,
    pub W: RelaxedPlonkWitness<C::Scalar>,
}

// TODO #31 docs
pub struct PlonkTrace<C: CurveAffine> {
    pub u: PlonkInstance<C>,
    pub w: PlonkWitness<C::Scalar>,
}

impl<C: CurveAffine> PlonkTrace<C> {
    pub fn to_relax(&self, k: usize) -> RelaxedPlonkTrace<C> {
        RelaxedPlonkTrace {
            U: self.u.to_relax(),
            W: self.w.to_relax(k),
        }
    }
}

impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO> for PlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point_iter(self.W_commitments.iter())
            .absorb_field_iter(self.instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_field_iter(self.challenges.iter().map(|cha| fe_to_fe(cha).unwrap()));
    }
}

impl<C: CurveAffine, RO: ROTrait<C::Base>> AbsorbInRO<C::Base, RO> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point_iter(self.W_commitments.iter())
            .absorb_point(&self.E_commitment)
            .absorb_field_iter(self.instance.iter().map(|inst| fe_to_fe(inst).unwrap()))
            .absorb_field_iter(self.challenges.iter().map(|cha| fe_to_fe(cha).unwrap()))
            .absorb_field(fe_to_fe(&self.u).unwrap());
    }
}

impl<F: PrimeField> PlonkStructure<F> {
    /// return the index offset of fixed variables(i.e. not folded)
    pub fn num_non_fold_vars(&self) -> usize {
        self.fixed_columns.len() + self.selectors.len()
    }

    /// return the number of variables to be folded
    /// each lookup argument will add 5 variables (l,t,m,h,g)
    pub fn num_fold_vars(&self) -> usize {
        self.num_advice_columns + 5 * self.num_lookups()
    }

    pub fn num_lookups(&self) -> usize {
        if self.lookup_arguments.is_none() {
            0
        } else {
            self.lookup_arguments.as_ref().unwrap().lookup_polys.len()
        }
    }

    /// indicates whether the original constrain system contains vector lookup
    pub fn has_vector_lookup(&self) -> bool {
        self.lookup_arguments
            .as_ref()
            .map(|arg| arg.has_vector_lookup)
            .unwrap_or(false)
    }

    pub fn is_sat<C, RO: ROTrait<C::Base>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
        U: &PlonkInstance<C>,
        W: &PlonkWitness<F>,
    ) -> Result<(), Error>
    where
        C: CurveAffine<ScalarExt = F>,
    {
        U.sps_verify(ro_nark)?;
        let check_commitments = U
            .W_commitments
            .iter()
            .zip(W.W.iter())
            .filter_map(|(Ci, Wi)| ck.commit(Wi).unwrap().ne(Ci).then_some(()))
            .count();

        let data = PlonkEvalDomain {
            num_advice: self.num_advice_columns,
            num_lookup: self.num_lookups(),
            challenges: U.challenges.clone(),
            selectors: &self.selectors,
            fixed: &self.fixed_columns,
            W1s: &W.W,
            W2s: &vec![],
        };
        let nrow = 2usize.pow(self.k as u32);
        let res = (0..nrow)
            .into_par_iter()
            .map(|row| data.eval(&self.poly, row))
            .collect::<Result<Vec<F>, _>>()
            .map(|v| v.into_iter().filter(|v| F::ZERO.ne(v)).count())?;

        let is_h_equal_g = self.is_sat_log_derivative(&W.W);

        match (res == 0, check_commitments == 0, is_h_equal_g) {
            (true, true, true) => Ok(()),
            (false, _, _) => Err(Error::EvaluationMismatch {
                mismatch_count: res,
                total_row: nrow,
            }),
            (_, _, false) => Err(Error::LogDerivativeNotSat),
            _ => Err(Error::CommitmentMismatch),
        }
    }

    pub fn is_sat_relaxed<C>(
        &self,
        ck: &CommitmentKey<C>,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), Error>
    where
        C: CurveAffine<ScalarExt = F>,
    {
        let check_W_commitments = U
            .W_commitments
            .iter()
            .zip(W.W.iter())
            .filter_map(|(Ci, Wi)| ck.commit(Wi).unwrap().ne(Ci).then_some(()))
            .count();

        let nrow = 2usize.pow(self.k as u32);
        let poly = self.poly.homogeneous(self.num_non_fold_vars());
        let data = PlonkEvalDomain {
            num_advice: self.num_advice_columns,
            num_lookup: self.num_lookups(),
            challenges: concat_vec!(&U.challenges, &[U.u]),
            selectors: &self.selectors,
            fixed: &self.fixed_columns,
            W1s: &W.W,
            W2s: &vec![],
        };
        let res = (0..nrow)
            .into_par_iter()
            .map(|row| data.eval(&poly, row))
            .collect::<Result<Vec<F>, _>>()
            .map(|v| {
                v.into_iter()
                    .enumerate()
                    .filter(|(i, v)| W.E[*i].ne(v))
                    .count()
            })?;
        let is_E_equal = ck.commit(&W.E).unwrap().eq(&U.E_commitment);
        let is_h_equal_g = self.is_sat_log_derivative(&W.W);

        match (res == 0, check_W_commitments == 0, is_E_equal, is_h_equal_g) {
            (true, true, true, true) => Ok(()),
            (false, _, _, _) => Err(Error::EvaluationMismatch {
                mismatch_count: res,
                total_row: nrow,
            }),
            (_, _, _, false) => Err(Error::LogDerivativeNotSat),
            _ => Err(Error::CommitmentMismatch),
        }
    }

    // permutation check for folding instance-witness pair
    pub fn is_sat_perm<C>(
        &self,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), Error>
    where
        C: CurveAffine<ScalarExt = F>,
    {
        let Z = U
            .instance
            .clone()
            .into_iter()
            .chain(W.W[0][..2usize.pow(self.k as u32) * self.num_advice_columns].to_vec())
            .collect::<Vec<_>>();
        let y = matrix_multiply(&self.permutation_matrix, &Z[..]);
        let mismatch_count = y
            .into_iter()
            .zip(Z)
            .map(|(y, z)| y - z)
            .filter(|d| F::ZERO.ne(d))
            .count();
        if mismatch_count == 0 {
            Ok(())
        } else {
            Err(Error::PermCheckFail { mismatch_count })
        }
    }

    /// check whether the log-derivative equation is satisfied
    pub fn is_sat_log_derivative(&self, W: &[Vec<F>]) -> bool {
        let nrow = 2usize.pow(self.k as u32);
        let check_is_zero = |hs: &[Vec<F>], gs: &[Vec<F>]| -> bool {
            hs.iter().zip(gs).all(|(h, g)| {
                // check sum_i h_i = sum_i g_i for each lookup
                h.iter()
                    .zip_eq(g)
                    .map(|(hi, gi)| *hi - *gi)
                    .sum::<F>()
                    .eq(&F::ZERO)
            })
        };
        let gather_vectors = |W: &Vec<F>, start_index: usize| -> Vec<Vec<F>> {
            iter::successors(Some(start_index), |idx| Some(idx + 2))
                .take(self.num_lookups())
                .map(|idx| W[idx * nrow..(idx * nrow + nrow)].to_vec())
                .collect::<Vec<_>>()
        };

        if self.has_vector_lookup() {
            let hs = gather_vectors(&W[2], 0);
            let gs = gather_vectors(&W[2], 1);
            check_is_zero(&hs, &gs)
        } else if self.num_lookups() > 0 {
            let hs = gather_vectors(&W[1], 0);
            let gs = gather_vectors(&W[1], 1);
            check_is_zero(&hs, &gs)
        } else {
            true
        }
    }

    pub fn get_degree_for_folding(&self) -> usize {
        let offset = self.num_non_fold_vars();
        self.poly.degree_for_folding(offset)
    }
}

impl<C: CurveAffine> PlonkInstance<C> {
    pub fn to_relax(&self) -> RelaxedPlonkInstance<C> {
        RelaxedPlonkInstance {
            W_commitments: self.W_commitments.clone(),
            E_commitment: C::identity(),
            instance: self.instance.clone(),
            challenges: self.challenges.clone(),
            u: C::ScalarExt::ONE,
        }
    }
}

impl<C: CurveAffine> RelaxedPlonkInstance<C> {
    pub fn new(num_io: usize, num_challenges: usize, num_witness: usize) -> Self {
        Self {
            W_commitments: vec![CommitmentKey::<C>::default_value(); num_witness],
            E_commitment: CommitmentKey::<C>::default_value(),
            instance: vec![C::ScalarExt::ZERO; num_io],
            challenges: vec![C::ScalarExt::ZERO; num_challenges],
            u: C::ScalarExt::ZERO,
        }
    }

    /// Folds a `RelaxedPlonkInstance` with another `PlonkInstance` while preserving their Plonk relation.
    ///
    /// This function combines the current relaxed Plonk instance with a given Plonk instance by
    /// computing new commitments, instances, and scalar values using provided cross-term
    /// commitments and random value `r`.
    ///
    /// # Arguments
    /// * `U2`: A `PlonkInstance` used to combine with the current relaxed Plonk instance.
    /// * `cross_term_commits`: The commitments of the cross terms used to calculate the folded
    /// value comm_E
    /// * `r`: A random scalar value used for combining the instances and commitments.
    ///
    /// # Returns
    /// The folded `RelaxedPlonkInstance` after combining the instances and commitments.
    /// for detail of how fold works, please refer to: [nifs](https://hackmd.io/d7syox5tTeaxkepc9nLvHw?view#31-NIFS)
    pub fn fold(&self, U2: &PlonkInstance<C>, cross_term_commits: &[C], r: &C::ScalarExt) -> Self {
        let W_commitments = self
            .W_commitments
            .iter()
            .zip(U2.W_commitments.clone())
            .enumerate()
            .map(|(W_index, (W1, W2))| {
                let rW = best_multiexp(&[*r], &[W2]).into();
                let res = *W1 + rW;
                debug!(
                    "W1 = {W1:?}; W2 = {W2:?}; rW2[{W_index}] = {rW:?}; rW1 + rW2 * r = {res:?}"
                );
                res.into()
            })
            .collect::<Vec<C>>();

        let instance = self
            .instance
            .par_iter()
            .zip(&U2.instance)
            .map(|(a, b)| *a + *r * b)
            .collect::<Vec<C::ScalarExt>>();

        let challenges = self
            .challenges
            .iter()
            .zip_eq(U2.challenges.iter())
            .map(|(a, b)| *a + *r * b)
            .collect::<Vec<C::ScalarExt>>();

        let u = self.u + *r;

        let comm_E = cross_term_commits
            .iter()
            .zip(iter::successors(Some(*r), |el| Some(*el * *r))) // r^1, r^2, ...
            .map(|(tk, power_of_r)| best_multiexp(&[power_of_r], &[*tk]).into())
            .fold(self.E_commitment, |acc, x| (acc + x).into());

        RelaxedPlonkInstance {
            W_commitments,
            E_commitment: comm_E,
            instance,
            u,
            challenges,
        }
    }
}

impl<F: PrimeField> PlonkWitness<F> {
    pub fn to_relax(&self, k: usize) -> RelaxedPlonkWitness<F> {
        let E = vec![F::ZERO; 2usize.pow(k as u32)];
        RelaxedPlonkWitness {
            W: self.W.clone(),
            E,
        }
    }
}

impl<F: PrimeField> RelaxedPlonkWitness<F> {
    /// round_sizes: specify the size of witness vector for each round
    /// in special soundness protocol.
    /// In current version, we have either one round (without lookup)
    /// or two rounds (with lookup)
    pub fn new(k: u32, round_sizes: &[usize]) -> Self {
        let mut W = Vec::new();
        let mut E = Vec::new();
        for sz in round_sizes.iter() {
            let tmp = vec![F::ZERO; *sz];
            W.push(tmp);
        }
        E.resize(2usize.pow(k), F::ZERO);
        Self { W, E }
    }

    pub fn fold(&self, W2: &PlonkWitness<F>, cross_terms: &[Vec<F>], r: &F) -> Self {
        let W = self
            .W
            .iter()
            .zip_eq(W2.W.iter())
            .map(|(vec1, vec2)| {
                vec1.par_iter()
                    .zip_eq(vec2.par_iter())
                    .map(|(w1, w2)| *w1 + *r * *w2)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let E = self
            .E
            .par_iter()
            .enumerate()
            .map(|(i, ei)| {
                cross_terms
                    .iter()
                    .zip(iter::successors(Some(*r), |el| Some(*el * r))) // r^1, r^2, ...
                    .fold(*ei, |acc, (tk, power_of_r)| acc + power_of_r * tk[i])
            })
            .collect::<Vec<_>>();

        RelaxedPlonkWitness { W, E }
    }
}
