//! # Special Soundness Protocol for Lookup Arguments
//!
//! This module implements a special soundness protocol for lookup arguments
//! within zero-knowledge proofs, utilizing a logarithmic derivative approach
//! to efficiently prove the inclusion of one set within another.
//!
//! ## Overview
//!
//! In zero-knowledge proofs, particularly those involving polynomial
//! commitments, lookup arguments are a crucial component. They allow a prover
//! to assert that a set of values (the lookup vector) is contained within
//! another set (the table vector), without revealing the actual values.
//!
//! The protocol follows the principles outlined in the "protostar" paper,
//! focusing on the use of logarithmic derivatives to compress multiple
//! expressions into a single polynomial.
//!
//! - [`Argument`]: Represents the lookup argument with compressed polynomials
//!   for both the lookup vector and the table vector.
//!
//! ## Functionality
//!
//! The module provides functions to:
//!
//! - Compress multiple lookup arguments into a single polynomial.
//! - Construct new structures with commitments based on the table vector.
//! - Calculate coefficients for the logarithmic derivative formula.
//! - Calculate inverse terms required for the protocol.
//! - Verify the satisfaction of the lookup argument.
//!
//! ## References
//!
//! - Lookup argument in [halo2](https://zcash.github.io/halo2/design/proving-system/lookup.html)
//! - IVC description in Section 4.3 in [Protostar](https://eprint.iacr.org/2023/620)
//! ## Notations
//!
//! Please see (#34)[https://github.com/snarkify/sirius/issues/34] for details on notations.
//!
use std::{
    array,
    collections::{HashMap, HashSet},
};

use ff::PrimeField;
use halo2_proofs::{plonk::ConstraintSystem, poly::Rotation};
use log::*;
use rayon::prelude::*;
use serde::Serialize;

use crate::{
    concat_vec,
    plonk::{
        eval::{Error, Eval, LookupEvalDomain},
        util::compress_halo2_expression,
    },
    polynomial::{Expression, Query},
    table::TableData,
};

/// Lookup Argument
///
/// Starting from vector lookup:
/// {(a_1, a_2, ..., a_k)} subset of {(t_1, t_2, ..., t_k)}
/// where:
/// - a_i are expressions over columns (x_1, ..., x_a)
/// - t_i are expressions over columns (y_1, ..., y_b)
///
/// We assume (y_1,...,y_b) are fixed columns.
/// Compress them
/// into a single (i.e. non-vector) Expression:
/// - lookup_poly = L(x_1,...,x_a) = a_1 + a_2*r + a_3*r^2 + ...
/// - table_poly  = T(y_1,...,y_b) = t_1 + t_2*r + t_3*r^2 + ...
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Arguments<F: PrimeField> {
    /// vector of the compressed lookup expressions
    /// L_i(x_1,...,x_{a_i})
    pub(crate) lookup_polys: Vec<Expression<F>>,
    /// vector of the table expressions
    /// T_i(y_1,...,y_{b_i})
    pub(crate) table_polys: Vec<Expression<F>>,
    /// has_vector_lookup = true if one of a_i > 1
    pub(crate) has_vector_lookup: bool,
}

impl<F: PrimeField> Arguments<F> {
    /// Compresses a potentially vector Lookup Argument from a constraint system into non-vector expression.
    pub fn compress_from(cs: &ConstraintSystem<F>) -> Option<Self> {
        let max_lookup_len = cs
            .lookups()
            .iter()
            .map(|arg| arg.input_expressions().len())
            .max()
            .filter(|l| *l != 0)?;

        let has_vector_lookup = max_lookup_len > 1;

        let (lookup_polys, table_polys) = cs
            .lookups()
            .iter()
            .map(|arg| {
                (
                    compress_halo2_expression(
                        arg.input_expressions(),
                        cs.num_selectors(),
                        cs.num_fixed_columns(),
                        // compress vector table items with r1 (challenge_index = 0)
                        0,
                    ),
                    compress_halo2_expression(
                        arg.table_expressions(),
                        cs.num_selectors(),
                        cs.num_fixed_columns(),
                        // compress vector lookups with r1 (challenge_index = 0)
                        0,
                    ),
                )
            })
            .unzip();

        Some(Self {
            lookup_polys,
            table_polys,
            has_vector_lookup,
        })
    }

    /// L_i(x1,...,xa) - l_i which evaluates to zero on every row
    /// T_i(y1,...,yb) - t_i which evaluates to zero on every row
    pub fn vanishing_lookup_polys(&self, cs: &ConstraintSystem<F>) -> Vec<Expression<F>> {
        let lookup_offset = cs.num_selectors() + cs.num_fixed_columns() + cs.num_advice_columns();
        let expression_of_l = |lookup_index: usize| -> Expression<F> {
            Expression::Polynomial(Query {
                index: lookup_offset + lookup_index * 5,
                rotation: Rotation(0),
            })
        };
        let expression_of_t = |lookup_index: usize| -> Expression<F> {
            Expression::Polynomial(Query {
                index: lookup_offset + lookup_index * 5 + 1,
                rotation: Rotation(0),
            })
        };

        let ls = self
            .lookup_polys
            .iter()
            .enumerate()
            .map(|(i, L_i)| L_i.clone() - expression_of_l(i))
            .collect::<Vec<_>>();

        let ts = self
            .table_polys
            .iter()
            .enumerate()
            .map(|(i, T_i)| T_i.clone() - expression_of_t(i))
            .collect::<Vec<_>>();
        concat_vec!(&ls, &ts)
    }

    pub fn num_lookups(&self) -> usize {
        self.lookup_polys.len()
    }

    /// calculate lhs and rhs of log-derivative relation
    /// each lookup argument introduces 1 extra "fixed" variables, 4 extra "advice" variables
    pub fn log_derivative_expr(
        &self,
        cs: &ConstraintSystem<F>,
        lookup_index: usize,
        challenge_index: usize,
    ) -> (Expression<F>, Expression<F>) {
        let r = Expression::Challenge(challenge_index);
        // starting index of lookup variables (l_i, t_i, m_i, h_i, g_i)
        let lookup_offset = cs.num_selectors() + cs.num_fixed_columns() + cs.num_advice_columns();
        // Please see (#34)[https://github.com/snarkify/sirius/issues/34] for details on notations.
        let [l, t, m, h, g] = array::from_fn(|idx| {
            Expression::Polynomial(Query {
                index: lookup_offset + lookup_index * 5 + idx,
                rotation: Rotation(0),
            })
        });
        // check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
        let lhs_rel = h * (l + r.clone()) - Expression::Constant(F::ONE);
        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let rhs_rel = g * (t + r) - m;
        (lhs_rel, rhs_rel)
    }

    /// collect the lhs and rhs of log-derivative relations from all lookup arguments
    pub fn log_derivative_lhs_and_rhs(&self, cs: &ConstraintSystem<F>) -> Vec<Expression<F>> {
        let challenge_index = if self.has_vector_lookup { 1 } else { 0 };
        (0..self.num_lookups())
            .flat_map(|lookup_index| {
                let (lhs, rhs) = self.log_derivative_expr(cs, lookup_index, challenge_index);
                vec![lhs, rhs].into_iter()
            })
            .collect::<Vec<_>>()
    }

    /// evaluate each of the lookup expressions to get vector l_i
    /// where l_i = L_i(x_1,...,x_a)
    fn evaluate_ls(&self, table: &TableData<F>, r: F) -> Result<Vec<Vec<F>>, Error> {
        let data = LookupEvalDomain {
            num_lookup: table.num_lookups(),
            challenges: vec![r],
            selectors: &table.selector,
            fixed: &table.fixed_columns,
            advice: &table.advice_columns,
        };

        let nrow = 2usize.pow(table.k);
        debug!("lookup_polys len: {} ", self.lookup_polys.len());
        self.lookup_polys
            .par_iter()
            .map(|expr| expr.expand())
            .map(|poly| {
                (0..nrow)
                    .into_par_iter()
                    .map(|row| data.eval(&poly, row))
                    .collect::<Result<Vec<F>, Error>>()
            })
            .collect()
    }

    /// evaluate each of the table expressions to get vector t_i
    /// where t_i = T(y1,...,y_b)
    fn evaluate_ts(&self, table: &TableData<F>, r: F) -> Result<Vec<Vec<F>>, Error> {
        let data = LookupEvalDomain {
            num_lookup: table.num_lookups(),
            challenges: vec![r],
            selectors: &table.selector,
            fixed: &table.fixed_columns,
            advice: &table.advice_columns,
        };
        let nrow = 2usize.pow(table.k);
        self.table_polys
            .par_iter()
            .map(|expr| expr.expand())
            .map(|poly| {
                (0..nrow)
                    .into_par_iter()
                    .map(|row| data.eval(&poly, row))
                    .collect::<Result<Vec<_>, Error>>()
            })
            .collect()
    }
    /// calculate the coefficients {m_i} in the log derivative formula
    /// m_i = sum_j \xi(w_j=t_i) assuming {t_i} have no duplicates
    fn evaluate_m(&self, l: &[F], t: &[F]) -> Vec<F> {
        debug!("evaluate_m: {} & {}", l.len(), t.len());
        let mut processed_t = HashSet::with_capacity(l.len().max(t.len()));

        let l_elements = l
            .iter()
            .fold(HashMap::with_capacity(l.len()), |mut acc, l_i| {
                *acc.entry(l_i.to_repr().as_ref().to_vec()).or_insert(0) += 1;
                acc
            });

        debug!("builded l_elements {}", l_elements.len());

        t.iter()
            .map(|t_i| {
                if processed_t.contains(t_i.to_repr().as_ref()) {
                    F::ZERO
                } else {
                    processed_t.insert(t_i.to_repr().as_ref().to_vec());

                    F::from_u128(
                        l_elements
                            .get(t_i.to_repr().as_ref())
                            .copied()
                            .unwrap_or_default() as u128,
                    )
                }
            })
            .collect()
    }

    fn evaluate_h_g(l: &[F], t: &[F], r: F, m: &[F]) -> (Vec<F>, Vec<F>) {
        let h = l
            .par_iter()
            .map(|&l_i| Option::from((l_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        let g = t
            .par_iter()
            .zip_eq(m.par_iter())
            .map(|(t_i, m_i)| *m_i * Option::from((*t_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        (h, g)
    }

    pub(crate) fn evaluate_coefficient_1(
        &self,
        table: &TableData<F>,
        r: F,
    ) -> Result<ArgumentCoefficient1<F>, Error> {
        debug!("start evaluate_coefficient_1");
        let ls = self.evaluate_ls(table, r)?;
        debug!("ls calculated: {}", ls.len());
        let ts = self.evaluate_ts(table, r)?;
        debug!("ts calculated: {}", ts.len());

        let mut ms = Vec::with_capacity(ls.len());
        ls.par_iter()
            .zip_eq(ts.par_iter())
            .map(|(l, t)| self.evaluate_m(l, t))
            .collect_into_vec(&mut ms);
        debug!("ms calculated");

        Ok(ArgumentCoefficient1 { ls, ts, ms })
    }
}

pub(crate) struct ArgumentCoefficient1<F: PrimeField> {
    pub ls: Vec<Vec<F>>,
    pub ts: Vec<Vec<F>>,
    pub ms: Vec<Vec<F>>,
}

impl<F: PrimeField> ArgumentCoefficient1<F> {
    /// calculate the inverse in log derivative formula
    /// h_i := \frac{1}{l_i+r}
    /// g_i := \frac{m_i}{t_i+r}
    pub(crate) fn evaluate_coefficient_2(&self, r: F) -> ArgumentCoefficient2<F> {
        let (hs, gs): (Vec<_>, Vec<_>) =
            itertools::multizip((self.ls.iter(), self.ts.iter(), self.ms.iter()))
                .par_bridge()
                .map(|(l, t, m)| Arguments::evaluate_h_g(l, t, r, m))
                .unzip();

        ArgumentCoefficient2 { hs, gs }
    }
}

pub(crate) struct ArgumentCoefficient2<F: PrimeField> {
    pub hs: Vec<Vec<F>>,
    pub gs: Vec<Vec<F>>,
}
