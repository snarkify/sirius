//! This module defines the TableData and Plonk related types for working with
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

use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    plonk::{
        eval::{Eval, PlonkEvalDomain},
        util::{cell_to_z_idx, column_index, compress_expression, fill_sparse_matrix},
    },
    polynomial::{
        sparse::{matrix_multiply, SparseMatrix},
        Expression, MultiPolynomial,
    },
    poseidon::{AbsorbInRO, ROTrait},
    util::{batch_invert_assigned, concatenate_with_padding, fe_to_fe},
};
use ff::{Field, PrimeField};
use halo2_proofs::{
    arithmetic::{best_multiexp, CurveAffine},
    circuit::Value,
    plonk::{
        Advice, Any, Assigned, Assignment, Challenge, Circuit, Column, ConstraintSystem, Error,
        Fixed, FloorPlanner, Instance, Selector,
    },
};
use itertools::Itertools;
use log::*;
use rayon::prelude::*;
use std::collections::HashMap;

use self::eval::EvalError;

pub mod eval;
pub mod lookup;
pub mod permutation;
pub mod util;

#[derive(Clone, PartialEq)]
pub struct PlonkStructure<C: CurveAffine> {
    /// k is a parameter such that 2^k is the total number of rows
    pub(crate) k: usize,
    pub(crate) selectors: Vec<Vec<bool>>,
    pub(crate) fixed_columns: Vec<Vec<C::ScalarExt>>,
    /// concatenate selectors and num_fixed_columns together, then commit
    pub(crate) fixed_commitment: C,

    pub(crate) num_advice_columns: usize,

    /// We follow the special soundness protocol(SPS), section 3.1 in [Protostar](https://eprint.iacr.org/2023/620)
    /// let k = num_challenges; when k > 0, we add extra verifier round, this is slightly different
    /// from protostar paper.
    /// see [`PlonkInstance::challenges`] for detail
    pub(crate) num_challenges: usize,
    /// specify the witness size of each prover round
    pub(crate) round_sizes: Vec<usize>,

    /// singla polynomial relation that combines custom gates and lookup relations
    pub(crate) poly: MultiPolynomial<C::ScalarExt>,
    pub(crate) permutation_matrix: SparseMatrix<C::ScalarExt>,
    pub(crate) lookup_arguments: Option<lookup::Arguments<C::ScalarExt>>,
}

#[derive(Clone, Debug)]
pub struct PlonkInstance<C: CurveAffine> {
    /// `W_commitments = round_sizes.len()`, see [`PlonkStructure.round_sizes`]
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
    U: RelaxedPlonkInstance<C>,
    W: RelaxedPlonkWitness<C::Scalar>,
}

// TODO #31 docs
pub struct PlonkTrace<C: CurveAffine> {
    u: PlonkInstance<C>,
    w: PlonkWitness<C::Scalar>,
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for PlonkStructure<C> {
    // TODO: add hash of other fields including gates
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_point(&self.fixed_commitment);
    }
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for PlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        for pt in self.W_commitments.iter() {
            ro.absorb_point(pt);
        }
        for inst in self.instance.iter() {
            ro.absorb_base(fe_to_fe(inst).unwrap());
        }
        for cha in self.challenges.iter() {
            ro.absorb_base(fe_to_fe(cha).unwrap());
        }
    }
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for RelaxedPlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        for pt in self.W_commitments.iter() {
            ro.absorb_point(pt);
        }
        ro.absorb_point(&self.E_commitment);
        for inst in self.instance.iter() {
            ro.absorb_base(fe_to_fe(inst).unwrap());
        }
        for cha in self.challenges.iter() {
            ro.absorb_base(fe_to_fe(cha).unwrap());
        }
        ro.absorb_base(fe_to_fe(&self.u).unwrap());
    }
}

impl<C: CurveAffine> PlonkStructure<C> {
    /// return the index offset of fixed variables(i.e. not folded)
    pub fn fixed_offset(&self) -> usize {
        self.fixed_columns.len() + self.selectors.len() + self.num_lookups()
    }

    /// return the number of variables to be folded
    /// each lookup argument will add 4 variables (l,m,h,g)
    pub fn num_fold_vars(&self) -> usize {
        self.num_advice_columns + 4 * self.num_lookups()
    }

    pub fn num_lookups(&self) -> usize {
        if self.lookup_arguments.is_none() {
            0
        } else {
            self.lookup_arguments.as_ref().unwrap().lookup_polys.len()
        }
    }

    /// run special soundness protocol for verifier
    pub fn run_sps_verifier<RO: ROTrait<C>>(
        &self,
        U: &PlonkInstance<C>,
        ro_nark: &mut RO,
    ) -> Result<(), SpsError> {
        if self.num_challenges == 0 {
            return Ok(());
        }

        U.instance.iter().for_each(|inst| {
            ro_nark.absorb_base(fe_to_fe(inst).unwrap());
        });
        for i in 0..self.num_challenges {
            ro_nark.absorb_point(&U.W_commitments[i]);
            let r = ro_nark.squeeze(NUM_CHALLENGE_BITS);
            if r != U.challenges[i] {
                return Err(SpsError::ChallengeNotMatch { challenge_index: i });
            }
        }
        Ok(())
    }

    pub fn is_sat<F, RO: ROTrait<C>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
        U: &PlonkInstance<C>,
        W: &PlonkWitness<F>,
    ) -> Result<(), DeciderError>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        self.run_sps_verifier(U, ro_nark)?;
        let check_commitments = U
            .W_commitments
            .iter()
            .zip(W.W.iter())
            .filter_map(|(Ci, Wi)| ck.commit(Wi).ne(Ci).then_some(()))
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

        match (res == 0, check_commitments == 0) {
            (true, true) => Ok(()),
            (false, _) => Err(DeciderError::EvaluationMismatch {
                mismatch_count: res,
                total_row: nrow,
            }),
            _ => Err(DeciderError::CommitmentMismatch),
        }
    }

    pub fn is_sat_relaxed<F>(
        &self,
        ck: &CommitmentKey<C>,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), DeciderError>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        let check_W_commitments = U
            .W_commitments
            .iter()
            .zip(W.W.iter())
            .filter_map(|(Ci, Wi)| ck.commit(Wi).ne(Ci).then_some(()))
            .count();

        let nrow = 2usize.pow(self.k as u32);
        let poly = self.poly.homogeneous(self.fixed_offset());
        let mut challenges = U.challenges.clone();
        challenges.push(U.u);
        let data = PlonkEvalDomain {
            num_advice: self.num_advice_columns,
            num_lookup: self.num_lookups(),
            challenges,
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
        let is_E_equal = ck.commit(&W.E).eq(&U.E_commitment);

        match (res == 0, check_W_commitments == 0, is_E_equal) {
            (true, true, true) => Ok(()),
            (false, _, _) => Err(DeciderError::EvaluationMismatch {
                mismatch_count: res,
                total_row: nrow,
            }),
            _ => Err(DeciderError::CommitmentMismatch),
        }
    }

    // permutation check for folding instance-witness pair
    pub fn is_sat_perm<F>(
        &self,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), String>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        let Z = U
            .instance
            .clone()
            .into_iter()
            // TODO(chao): fix the case when W = advice||(l_i,m_i)
            .chain(W.W[0].clone())
            .collect::<Vec<_>>();
        let y = matrix_multiply(&self.permutation_matrix, &Z[..]);
        let diff = y
            .into_iter()
            .zip(Z)
            .map(|(y, z)| y - z)
            .filter(|d| F::ZERO.ne(d))
            .count();
        if diff == 0 {
            Ok(())
        } else {
            Err("permutation check failed".to_string())
        }
    }

    pub fn is_sat_lookup<F>(
        &self,
        _ck: &CommitmentKey<C>,
        _U: &RelaxedPlonkInstance<C>,
        _W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), String>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        todo!()
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
            challenges: vec![C::ScalarExt::ONE; num_challenges],
            u: C::ScalarExt::ONE,
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

#[derive(Debug)]
pub struct TableData<F: PrimeField> {
    // TODO: without usable_rows still safe?
    pub(crate) k: u32,
    pub(crate) cs: ConstraintSystem<F>,
    pub(crate) fixed: Vec<Vec<Assigned<F>>>,
    pub(crate) fixed_columns: Vec<Vec<F>>,
    pub(crate) selector: Vec<Vec<bool>>,
    pub(crate) instance: Vec<F>,
    pub(crate) advice: Vec<Vec<Assigned<F>>>,
    pub(crate) advice_columns: Vec<Vec<F>>,
    pub(crate) challenges: HashMap<usize, F>,
    pub(crate) permutation: Option<permutation::Assembly>,
    pub(crate) lookup_arguments: Option<lookup::Arguments<F>>,
}

impl<F: PrimeField> TableData<F> {
    pub fn new(k: u32, instance: Vec<F>) -> Self {
        let cs = ConstraintSystem::default();
        TableData {
            k,
            cs,
            instance,
            fixed: vec![],
            fixed_columns: vec![],
            selector: vec![],
            advice: vec![],
            advice_columns: vec![],
            challenges: HashMap::new(),
            permutation: None,
            lookup_arguments: None,
        }
    }

    /// indicates whether the original constrain system contains vector lookup
    pub fn has_vector_lookup(&self) -> bool {
        self.lookup_arguments
            .as_ref()
            .map(|arg| arg.has_vector_lookup)
            .unwrap_or(false)
    }

    pub fn num_lookups(&self) -> usize {
        if self.lookup_arguments.is_none() {
            0
        } else {
            self.lookup_arguments.as_ref().unwrap().lookup_polys.len()
        }
    }

    pub fn lookup_exprs(&self, cs: &ConstraintSystem<F>) -> Vec<Expression<F>> {
        let mut combined = vec![];
        if let Some(lookup_arguments) = self.lookup_arguments.as_ref() {
            combined = lookup_arguments.lookup_polys_minus_l(cs);
            combined.extend(lookup_arguments.log_derivative_lhs_and_rhs(cs));
        }
        combined
    }

    /// Prepares the constraint system for a new configuration.
    ///
    /// This function initializes various components of the constraint system
    /// such as the permutation assembly, lookup arguments, and column vectors
    /// for fixed, selector, and advice columns based on the provided configuration.
    /// It must be called before using the constraint system for any computations.
    ///
    /// # Arguments
    ///
    /// * `configure` - A closure that takes a mutable reference to the `ConstraintSystem`
    ///   and returns a configuration object `C`. This allows for flexible and customized
    ///   setup of the constraint system.
    ///
    /// # Returns
    ///
    /// Returns the configuration object `C` as determined by the `configure` closure.
    ///
    /// # Panics
    ///
    /// This function will panic if the number of instance columns is not equal to 1.
    /// This is a temporary restriction and support for user-defined instance columns
    /// should be added in the future.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// // Assuming `cs` is a mutable reference to a ConstraintSystem object
    /// let config = cs.prepare(|cs| {
    ///     // Configure the constraint system
    ///     // ...
    ///     ConcreteCircuit::configure(cs)
    /// });
    /// ```
    pub(crate) fn prepare_assembly<C>(
        &mut self,
        configure: impl FnOnce(&mut ConstraintSystem<F>) -> C,
    ) -> C {
        let config = configure(&mut self.cs);
        self.permutation = Some(permutation::Assembly::new(
            1 << self.k,
            &self.cs.permutation,
        ));
        self.lookup_arguments = lookup::Arguments::compress_from(&self.cs);
        let n = 1 << self.k;
        // TODO: add support for user defined instance columns
        assert!(self.cs.num_instance_columns() == 1);
        self.fixed = vec![vec![F::ZERO.into(); n]; self.cs.num_fixed_columns()];
        self.selector = vec![vec![false; n]; self.cs.num_selectors()];
        self.advice = vec![vec![F::ZERO.into(); n]; self.cs.num_advice_columns()];
        config
    }

    // TODO Change design
    pub(crate) fn postpone_assembly(&mut self) {
        self.fixed_columns = batch_invert_assigned(&self.fixed);
        self.advice_columns = batch_invert_assigned(&self.advice);
    }

    pub fn assembly<ConcreteCircuit: Circuit<F>>(
        &mut self,
        circuit: &ConcreteCircuit,
    ) -> Result<(), Error> {
        let config = self.prepare_assembly(ConcreteCircuit::configure);

        ConcreteCircuit::FloorPlanner::synthesize(
            self,
            circuit,
            config.clone(),
            vec![], // TODO: make sure constants not needed
        )?;

        self.postpone_assembly();

        Ok(())
    }

    pub fn plonk_structure<C: CurveAffine<ScalarExt = F>>(
        &self,
        ck: &CommitmentKey<C>,
    ) -> PlonkStructure<C> {
        assert!(
            !self.advice.is_empty(),
            "should call TableData.assembly() first"
        );
        let selectors = self.selector.clone();
        let selector_columns =
            self.selector
                .iter()
                .flatten()
                .map(|sel| if *sel { F::ONE } else { F::ZERO });
        // TODO: avoid clone
        let fixed_commitment = ck.commit(
            &self
                .fixed_columns
                .clone()
                .into_iter()
                .flatten()
                .chain(selector_columns)
                .collect::<Vec<_>>(),
        );

        let num_gates = self
            .cs
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter())
            .count();
        let num_lookups = self.num_lookups();
        // we have at most 3 challenges: see [`PlonkInstance.challenges`]
        let num_challenges = if self.has_vector_lookup() {
            3
        } else if num_lookups > 0 {
            2
        } else if num_gates > 1 {
            1
        } else {
            0
        };

        // we have at most 3 prover rounds
        let nrow = 2usize.pow(self.k);
        let mut round_sizes = Vec::new();
        if self.has_vector_lookup() {
            // advice columns
            round_sizes.push(self.cs.num_advice_columns() * nrow);
            // (l_i, m_i), see [`lookup.rs::Arguments::log_derivative_expr`]
            round_sizes.push(2 * num_lookups * nrow);
            // (h_i, g_i), see [`lookup.rs::Arguments::log_derivative_expr`]
            round_sizes.push(2 * num_lookups * nrow);
        } else if num_lookups > 0 {
            // advice columns || (l_i, m_i)
            round_sizes.push((self.cs.num_advice_columns() + 2 * num_lookups) * nrow);
            // (h_i, g_i)
            round_sizes.push(2 * num_lookups * nrow);
        } else {
            // advice columns
            round_sizes.push(self.cs.num_advice_columns() * nrow);
        };

        let exprs = self
            .cs
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter().cloned())
            .map(|expr| {
                Expression::from_halo2_expr(
                    &expr,
                    self.cs.num_selectors(),
                    self.cs.num_fixed_columns(),
                    self.num_lookups(),
                )
            })
            .chain(self.lookup_exprs(&self.cs))
            .collect::<Vec<_>>();

        // we use r3 to combine all custom gates and lookup expressions
        // find the challenge index of r3
        let challenge_index = if num_challenges > 0 {
            num_challenges - 1
        } else {
            0
        };
        let poly = compress_expression(&exprs, challenge_index).expand();
        let permutation_matrix = self.permutation_matrix();

        PlonkStructure {
            k: self.k as usize,
            selectors,
            fixed_columns: self.fixed_columns.clone(),
            num_advice_columns: self.cs.num_advice_columns(),
            num_challenges,
            round_sizes,
            poly,
            fixed_commitment,
            permutation_matrix,
            lookup_arguments: self.lookup_arguments.clone(),
        }
    }

    /// run 0-round special soundness protocol
    /// w.r.t single custom gate + no lookup
    fn run_sps_protocol_0<C: CurveAffine<ScalarExt = F>>(
        &self,
        ck: &CommitmentKey<C>,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        let W1 = concatenate_with_padding(&self.advice_columns, 2usize.pow(self.k));
        let C1 = ck.commit(&W1);

        Ok((
            PlonkInstance {
                W_commitments: vec![C1],
                instance: self.instance.clone(),
                challenges: vec![],
            },
            PlonkWitness { W: vec![W1] },
        ))
    }

    /// run 1-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C] -> ]r1[
    /// w.r.t multiple gates + no lookup
    fn run_sps_protocol_1<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        let (mut plonk_instance, plonk_witness) = self.run_sps_protocol_0(ck)?;

        self.instance.iter().for_each(|inst| {
            ro_nark.absorb_base(fe_to_fe(inst).unwrap());
        });
        plonk_instance.W_commitments.iter().for_each(|C| {
            ro_nark.absorb_point(C);
        });

        plonk_instance
            .challenges
            .push(ro_nark.squeeze(NUM_CHALLENGE_BITS));

        Ok((plonk_instance, plonk_witness))
    }

    /// run 2-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C1] -> ]r1[ -> [C2] -> ]r2[
    /// w.r.t has lookup but no vector lookup
    fn run_sps_protocol_2<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        let k_power_of_2 = 2usize.pow(self.k);

        // round 1
        let lookup_coeff = self
            .lookup_arguments
            .as_ref()
            .map(|la| la.evaluate_coefficient_1(self, F::ZERO))
            .transpose()?
            .ok_or(SpsError::LackOfLookupArguments)?;

        let W1 = [
            concatenate_with_padding(&self.advice_columns, k_power_of_2),
            concatenate_with_padding(&lookup_coeff.ls, k_power_of_2),
            concatenate_with_padding(&lookup_coeff.ms, k_power_of_2),
        ]
        .concat();

        let C1 = ck.commit(&W1);

        self.instance.iter().for_each(|inst| {
            ro_nark.absorb_base(fe_to_fe(inst).unwrap());
        });
        ro_nark.absorb_point(&C1);
        let r1 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        // round 2
        let lookup_coeff = lookup_coeff.evaluate_coefficient_2(r1);

        let W2 = [
            concatenate_with_padding(&lookup_coeff.hs, k_power_of_2),
            concatenate_with_padding(&lookup_coeff.gs, k_power_of_2),
        ]
        .concat();

        let C2 = ck.commit(&W2);
        ro_nark.absorb_point(&C2);
        let r2 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        Ok((
            PlonkInstance {
                W_commitments: vec![C1, C2],
                instance: self.instance.clone(),
                challenges: vec![r1, r2],
            },
            PlonkWitness { W: vec![W1, W2] },
        ))
    }

    /// run 3-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C1] -> ]r1[ -> [C2] -> ]r2[ -> [C3] -> ]r3[
    fn run_sps_protocol_3<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        self.instance.iter().for_each(|inst| {
            ro_nark.absorb_base(fe_to_fe(inst).unwrap());
        });

        let k_power_of_2 = 2usize.pow(self.k);

        // round 1
        let W1 = concatenate_with_padding(&self.advice_columns, k_power_of_2);
        let C1 = ck.commit(&W1);
        ro_nark.absorb_point(&C1);
        let r1 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        // round 2
        let lookup_coeff = self
            .lookup_arguments
            .as_ref()
            .map(|la| la.evaluate_coefficient_1(self, r1))
            .transpose()?
            .ok_or(SpsError::LackOfLookupArguments)?;

        let W2 = [
            concatenate_with_padding(&lookup_coeff.ls, k_power_of_2),
            concatenate_with_padding(&lookup_coeff.ms, k_power_of_2),
        ]
        .concat();
        let C2 = ck.commit(&W2);
        ro_nark.absorb_point(&C2);
        let r2 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        // round 3
        let lookup_coef = lookup_coeff.evaluate_coefficient_2(r2);

        let W3 = [
            concatenate_with_padding(&lookup_coef.hs, k_power_of_2),
            concatenate_with_padding(&lookup_coef.gs, k_power_of_2),
        ]
        .concat();

        let C3 = ck.commit(&W3);
        ro_nark.absorb_point(&C3);
        let r3 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        Ok((
            PlonkInstance {
                W_commitments: vec![C1, C2, C3],
                instance: self.instance.clone(),
                challenges: vec![r1, r2, r3],
            },
            PlonkWitness {
                W: vec![W1, W2, W3],
            },
        ))
    }

    /// run special soundness protocol to generate witnesses and challenges
    /// depending on whether we have multiple gates, lookup arguments and whether
    /// we have vector lookup, we will call different sub-sps protocol
    pub fn run_sps_protocol<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
        num_challenges: usize,
    ) -> Result<(PlonkInstance<C>, PlonkWitness<F>), SpsError> {
        if self.advice.is_empty() {
            return Err(SpsError::LackOfAdvices);
        }

        match num_challenges {
            0 => self.run_sps_protocol_0(ck),
            1 => self.run_sps_protocol_1(ck, ro_nark),
            2 => self.run_sps_protocol_2(ck, ro_nark),
            3 => self.run_sps_protocol_3(ck, ro_nark),
            challenges_count => Err(SpsError::UnsupportedChallengesCount { challenges_count }),
        }
    }

    /// construct sparse matrix P (size N*N) from copy constraints
    /// since folding will change values of advice/instance column while keep fixed column values
    /// we don't allow fixed column to be in the copy constraint here
    /// suppose we have 1 instance column, n advice columns
    /// and there are total of r rows. notice the instance column only contains `num_io = io` items
    /// N = num_io + r*n. Let (i_1,...,i_{io}) be all values of the instance columns
    /// and (x_1,...,x_{n*r}) be concatenate of advice columns.
    /// define vector Z = (i_1,...,i_{io}, x_1,...,x_{n*r})
    /// This function is to find the permutation matrix P such that the copy constraints are
    /// equivalent to P * Z - Z = 0. This is invariant relation under our folding scheme
    fn permutation_matrix(&self) -> SparseMatrix<F> {
        let mut sparse_matrix_p = Vec::new();
        let num_advice = self.cs.num_advice_columns();
        let num_rows = self.advice[0].len();
        let num_io = self.instance.len();
        let columns = &self.cs.permutation.columns;

        for (left_col, vec) in self
            .permutation
            .as_ref()
            .unwrap()
            .mapping
            .iter()
            .enumerate()
        {
            for (left_row, cycle) in vec.iter().enumerate() {
                // skip because we don't account for row that beyond the num_io in instance column
                if left_col == 0 && left_row >= num_io {
                    continue;
                }
                let left_col = column_index(left_col, columns);
                let right_col = column_index(cycle.0, columns);
                let left_z_idx = cell_to_z_idx(left_col, left_row, num_rows, num_io);
                let right_z_idx = cell_to_z_idx(right_col, cycle.1, num_rows, num_io);
                sparse_matrix_p.push((left_z_idx, right_z_idx, F::ONE));
            }
        }

        fill_sparse_matrix(&mut sparse_matrix_p, num_advice, num_rows, num_io, columns);
        sparse_matrix_p
    }
}

impl<F: PrimeField> Assignment<F> for TableData<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.selector[selector.index()][row] = true;
        Ok(())
    }

    fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        assert!(column.index() == 0); // require just single instance
        self.instance
            .get(row)
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // TODO: support phases
        *self
            .advice
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or_else(|| {
                error!(
                    "Error while assign advice {} in column {column:?} & row {row}",
                    annotation().into()
                );
                Error::BoundsFailure
            })? = to().into_field().assign()?;

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        *self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or_else(|| {
                error!(
                    "Error while assign fixed {} in column {column:?} & row {row}",
                    annotation().into()
                );
                Error::BoundsFailure
            })? = to().into_field().assign()?;
        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        if let Some(permutation) = self.permutation.as_mut() {
            permutation.copy(left_column, left_row, right_column, right_row)
        } else {
            error!("permutation is not initialized properly");
            Err(Error::Synthesis)
        }
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, challenge: Challenge) -> Value<F> {
        self.challenges
            .get(&challenge.index())
            .cloned()
            .map(Value::known)
            .unwrap_or_else(Value::unknown)
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SpsError {
    #[error(transparent)]
    Eval(#[from] EvalError),
    #[error("Sps verification fail: challenge not match")]
    ChallengeNotMatch { challenge_index: usize },
    #[error("For this challenges count table must have lookup aguments")]
    LackOfLookupArguments,
    #[error("Lack of advices, should call `TableData::assembly` first")]
    LackOfAdvices,
    #[error("Only 0..=3 num of challenges supported: {challenges_count} not")]
    UnsupportedChallengesCount { challenges_count: usize },
}

#[derive(Debug, thiserror::Error)]
pub enum DeciderError {
    #[error(transparent)]
    Sps(#[from] SpsError),
    #[error(transparent)]
    Eval(#[from] EvalError),
    #[error("(Relaxed) plonk relation not satisfied: commitment mismatch")]
    CommitmentMismatch,
    #[error("(Relaxed) plonk relation not satisfied: commitment mismatch")]
    EvaluationMismatch {
        mismatch_count: usize,
        total_row: usize,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};
    use crate::util::trim_leading_zeros;
    use ff::PrimeField;
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Instance};
    use halo2curves::group::ff::FromUniformBytes;
    use prettytable::{row, Cell, Row, Table};

    const T: usize = 3;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
        pconfig: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    struct TestCircuit<F: PrimeField> {
        inputs: Vec<F>,
        r: F,
    }

    impl<F: PrimeField> TestCircuit<F> {
        fn new(inputs: Vec<F>, r: F) -> Self {
            Self { inputs, r }
        }
    }

    impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: Vec::new(),
                r: F::ZERO,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let pconfig = MainGate::configure(meta);
            Self::Config { pconfig, instance }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let pchip = MainGate::new(config.pconfig);
            let output = layouter.assign_region(
                || "test",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    pchip.random_linear_combination(ctx, self.inputs.clone(), self.r)
                },
            )?;
            layouter.constrain_instance(output.cell(), config.instance, 0)?;
            Ok(())
        }
    }

    #[test]
    fn test_assembly() {
        use ff::Field;
        use halo2curves::pasta::Fp;

        const K: u32 = 4;
        let mut inputs = Vec::new();
        for i in 1..10 {
            inputs.push(Fp::from(i as u64));
        }
        let circuit = TestCircuit::new(inputs, Fp::ONE);
        let output = Fp::from_str_vartime("45").unwrap();
        let public_inputs = vec![output];

        let mut td = TableData::<Fp>::new(K, public_inputs);
        let _ = td.assembly(&circuit);

        let mut table = Table::new();
        table.add_row(row!["s0", "s1", "s2", "in", "out"]);
        let col = 5;
        for i in 0..2usize.pow(K) {
            let mut row = vec![];
            for j in 0..col {
                if let Some(val) = td.advice.get(j).and_then(|v| v.get(i)) {
                    row.push(trim_leading_zeros(format!("{:?}", val.evaluate())));
                }
            }
            table.add_row(Row::new(row.iter().map(|s| Cell::new(s)).collect()));
        }
        // table.printstd();
    }
}
