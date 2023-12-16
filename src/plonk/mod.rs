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
use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    plonk::util::{cell_to_z_idx, column_index, compress_expression, fill_sparse_matrix},
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
    /// see [`PlonkInstance.challenges`] for detail
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

/// Used for evaluate plonk custom gates
pub struct PlonkEvalDomain<'a, C: CurveAffine, F: PrimeField> {
    pub(crate) S: &'a PlonkStructure<C>,
    pub(crate) U1: &'a RelaxedPlonkInstance<C>,
    pub(crate) W1: &'a RelaxedPlonkWitness<F>,
    pub(crate) U2: &'a RelaxedPlonkInstance<C>,
    pub(crate) W2: &'a RelaxedPlonkWitness<F>,
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
        ro.absorb_point(self.fixed_commitment);
    }
}

impl<C: CurveAffine, RO: ROTrait<C>> AbsorbInRO<C, RO> for PlonkInstance<C> {
    fn absorb_into(&self, ro: &mut RO) {
        for pt in self.W_commitments.iter() {
            ro.absorb_point(*pt);
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
            ro.absorb_point(*pt);
        }
        ro.absorb_point(self.E_commitment);
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

    pub fn is_sat<F>(
        &self,
        ck: &CommitmentKey<C>,
        U: &PlonkInstance<C>,
        W: &PlonkWitness<F>,
    ) -> Result<(), String>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        let nrow = 2usize.pow(self.k as u32);
        let U2 = RelaxedPlonkInstance::new(
            U.instance.len(),
            self.num_challenges,
            self.round_sizes.len(),
        );
        let W2 = RelaxedPlonkWitness::new(self.k as u32, &self.round_sizes);
        let data = PlonkEvalDomain {
            S: self,
            U1: &U.to_relax(),
            W1: &W.to_relax(self.k),
            U2: &U2,
            W2: &W2,
        };
        let res: usize = (0..nrow)
            .into_par_iter()
            .map(|row| self.poly.eval(row, &data))
            .filter(|v| F::ZERO.ne(v))
            .count();

        if U.W_commitments[0] == ck.commit(&W.W[0]) && res == 0 {
            Ok(())
        } else {
            Err("plonk relation not satisfied".to_string())
        }
    }

    pub fn is_sat_relaxed<F>(
        &self,
        ck: &CommitmentKey<C>,
        U: &RelaxedPlonkInstance<C>,
        W: &RelaxedPlonkWitness<F>,
    ) -> Result<(), String>
    where
        C: CurveAffine<ScalarExt = F>,
        F: PrimeField,
    {
        let nrow = 2usize.pow(self.k as u32);
        let U2 = RelaxedPlonkInstance::new(
            U.instance.len(),
            self.num_challenges,
            self.round_sizes.len(),
        );
        let W2 = RelaxedPlonkWitness::new(self.k as u32, &self.round_sizes);
        let poly = self.poly.homogeneous(self.fixed_offset());
        let data = PlonkEvalDomain {
            S: self,
            U1: U,
            W1: W,
            U2: &U2,
            W2: &W2,
        };
        let res: usize = (0..nrow)
            .into_par_iter()
            .map(|row| poly.eval(row, &data))
            .enumerate()
            .filter(|(i, v)| W.E[*i].ne(v))
            .count();

        let actual_W_commit = ck.commit(&W.W[0]);
        let actual_E_commit = ck.commit(&W.E);

        match (
            res == 0,
            U.W_commitments[0].eq(&actual_W_commit),
            U.E_commitment.eq(&actual_E_commit),
        ) {
            (true, true, true) => Ok(()),
            (false, _, _) => Err(format!(
                "relaxed plonk relation not satisfied on {} out of {} rows",
                res, nrow
            )),
            (true, false, false) => Err(format!(
                "both commitment of witnesses W & E is not match:
                    W: Expected: {:?}, Actual: {:?},
                    E: Expected: {:?}, Actual: {:?}",
                U.W_commitments[0], actual_W_commit, U.E_commitment, actual_E_commit
            )),
            (true, false, true) => Err(format!(
                "commitment of witness W is not match: Expected: {:?}, Actual: {:?}",
                U.W_commitments[0], actual_W_commit
            )),
            (true, true, false) => Err(format!(
                "commitment of witness E is not match: Expected: {:?}, Actual: {:?}",
                U.E_commitment, actual_E_commit
            )),
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
            .map(|(W1, W2)| *W1 + best_multiexp(&[*r], &[W2]).into())
            .map(|W| W.into())
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
            .enumerate()
            .map(|(k, tk)| best_multiexp(&[r.pow([k as u64 + 1, 0, 0, 0])], &[*tk]).into())
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
            .zip(W2.W.iter())
            .map(|(vec1, vec2)| {
                vec1.par_iter()
                    .zip(vec2.par_iter())
                    .map(|(w1, w2)| *w1 + *r * *w2)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let E = self
            .E
            .par_iter()
            .enumerate()
            .map(|(i, ei)| {
                let mut r_power = F::ONE;
                cross_terms.iter().fold(*ei, |acc, tk| {
                    r_power *= *r;
                    acc + r_power * tk[i]
                })
            })
            .collect::<Vec<_>>();

        RelaxedPlonkWitness { W, E }
    }
}

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
            combined = lookup_arguments.lookup_polys.clone();
            combined.extend(lookup_arguments.log_derivative_lhs(cs));
        }
        combined
    }

    pub fn assembly<ConcreteCircuit: Circuit<F>>(
        &mut self,
        circuit: &ConcreteCircuit,
    ) -> Result<(), Error> {
        let config = ConcreteCircuit::configure(&mut self.cs);
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
        ConcreteCircuit::FloorPlanner::synthesize(
            self,
            circuit,
            config.clone(),
            vec![], // TODO: make sure constants not needed
        )?;
        self.fixed_columns = batch_invert_assigned(&self.fixed);
        self.advice_columns = batch_invert_assigned(&self.advice);
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
        let cha_index = if num_challenges > 0 {
            num_challenges - 1
        } else {
            0
        };
        let poly = compress_expression(&exprs[..], cha_index).expand();
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
    /// i.e no need to generate challenge
    pub fn run_sps_protocol_0<C: CurveAffine<ScalarExt = F>>(
        &self,
        ck: &CommitmentKey<C>,
    ) -> (PlonkInstance<C>, PlonkWitness<F>) {
        assert!(
            !self.advice.is_empty(),
            "should call TableData.assembly() first"
        );

        let W1 = concatenate_with_padding(&self.advice_columns, 2usize.pow(self.k));
        let C1 = ck.commit(&W1);

        (
            PlonkInstance {
                W_commitments: vec![C1],
                instance: self.instance.clone(),
                challenges: vec![],
            },
            PlonkWitness { W: vec![W1] },
        )
    }

    /// run 3-round special soundness protocol to generate witnesses and challenges
    /// notations: "[C]" absorb C; "]r[" squeeze r;
    /// sequence of generating challenges:
    /// [pi.instance] -> [C1] -> ]r1[ -> [C2] -> ]r2[ -> [C3] -> ]r3[
    pub fn run_sps_protocol_3<C: CurveAffine<ScalarExt = F>, RO: ROTrait<C>>(
        &self,
        ck: &CommitmentKey<C>,
        ro_nark: &mut RO,
    ) -> (PlonkInstance<C>, PlonkWitness<F>) {
        assert!(
            !self.advice.is_empty(),
            "should call TableData.assembly() first"
        );

        let _ = self.instance.iter().map(|inst| {
            ro_nark.absorb_base(fe_to_fe(inst).unwrap());
        });

        // round 1
        let W1 = concatenate_with_padding(&self.advice_columns[..], 2usize.pow(self.k));
        let C1 = ck.commit(&W1);
        ro_nark.absorb_point(C1);
        let r1 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        // round 2
        let lookup_arguments = self.lookup_arguments.as_ref().unwrap();
        let ls = lookup_arguments.evaluate_ls(self, r1);
        let ts = lookup_arguments.evaluate_ts(self, r1);
        let ms = ls
            .iter()
            .zip(ts.iter())
            .map(|(l, t)| lookup_arguments.evaluate_m(l, t))
            .collect::<Vec<_>>();
        let mut W2 = concatenate_with_padding(&ls, 2usize.pow(self.k));
        let W2_1 = concatenate_with_padding(&ms, 2usize.pow(self.k));
        W2.extend(W2_1);
        let C2 = ck.commit(&W2);
        ro_nark.absorb_point(C2);
        let r2 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        // round 3
        let mut hs: Vec<Vec<F>> = Vec::new();
        let mut gs: Vec<Vec<F>> = Vec::new();
        for ((l, t), m) in ls.iter().zip(ts.iter()).zip(ms.iter()) {
            let (h, g) = lookup_arguments.evaluate_h_g(l, t, r2, m);
            hs.push(h);
            gs.push(g);
        }
        let mut W3 = concatenate_with_padding(&hs, 2usize.pow(self.k));
        let W3_1 = concatenate_with_padding(&gs, 2usize.pow(self.k));
        W3.extend(W3_1);
        let C3 = ck.commit(&W3);
        ro_nark.absorb_point(C3);
        let r3 = ro_nark.squeeze(NUM_CHALLENGE_BITS);

        (
            PlonkInstance {
                W_commitments: vec![C1, C2, C3],
                instance: self.instance.clone(),
                challenges: vec![r1, r2, r3],
            },
            PlonkWitness {
                W: vec![W1, W2, W3],
            },
        )
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
        _: A,
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
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
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
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;
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
