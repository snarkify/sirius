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

use ff::PrimeField;
use halo2_proofs::{plonk::ConstraintSystem, poly::Rotation};
use rayon::prelude::*;
use std::array;

use crate::{
    plonk::util::compress_halo2_expression,
    plonk::TableData,
    polynomial::{Expression, Query},
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
#[derive(Clone, PartialEq)]
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
        let num_lookups = cs.lookups().len();

        let (lookup_polys, table_polys) = cs
            .lookups()
            .iter()
            .map(|arg| {
                (
                    compress_halo2_expression(
                        arg.table_expressions(),
                        cs.num_selectors(),
                        cs.num_fixed_columns(),
                        num_lookups,
                        // compress vector table items with r1 (cha_index = 0)
                        0,
                    ),
                    compress_halo2_expression(
                        arg.input_expressions(),
                        cs.num_selectors(),
                        cs.num_fixed_columns(),
                        num_lookups,
                        // compress vector lookups with r1 (cha_index = 0)
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

    pub fn num_lookups(&self) -> usize {
        self.lookup_polys.len()
    }

    /// calculate lhs and rhs of log-derivative relation
    /// each lookup argument introduces 1 extra "fixed" variables, 4 extra "advice" variables
    pub fn log_derivative_expr(
        &self,
        cs: &ConstraintSystem<F>,
        lookup_index: usize,
        cha_index: usize,
    ) -> (Expression<F>, Expression<F>) {
        let r = Expression::Challenge(cha_index);
        // starting index of lookup variables (l_i, m_i, h_i, g_i)
        let lookup_offset = cs.num_selectors()
            + cs.num_fixed_columns()
            + self.num_lookups()
            + cs.num_advice_columns();
        let t = Expression::Polynomial(Query {
            index: cs.num_selectors() + cs.num_fixed_columns() + lookup_index,
            rotation: Rotation(0),
        });
        let [l, m, h, g] = array::from_fn(|idx| {
            Expression::Polynomial(Query {
                index: lookup_offset + lookup_index * 4 + idx,
                rotation: Rotation(0),
            })
        });
        // check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
        let lhs_rel = h * (l + r.clone()) - Expression::Constant(F::ONE);
        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let rhs_rel = g * (t + r) - m;
        (lhs_rel, rhs_rel)
    }

    /// collect lhs of log-derivative relations from all lookup arguments
    pub fn log_derivative_lhs(&self, cs: &ConstraintSystem<F>) -> Vec<Expression<F>> {
        let cha_index = if self.has_vector_lookup { 1 } else { 0 };
        (0..self.num_lookups())
            .map(|lookup_index| self.log_derivative_expr(cs, lookup_index, cha_index).0)
            .collect()
    }

    /// evaluate each of the lookup expressions to get vector l_i
    /// where l_i = L_i(x_1,...,x_a)
    pub fn evaluate_ls(&self, table: &TableData<F>, r: F) -> Vec<Vec<F>> {
        let data = LookupEvalDomain { table, r };
        let nrow = 2usize.pow(table.k);
        self.lookup_polys
            .iter()
            .map(|expr| expr.expand())
            .map(|poly| {
                (0..nrow)
                    .into_par_iter()
                    .map(|row| poly.eval(row, &data))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }

    /// evaluate each of the table expressions to get vector t_i
    /// where t_i = T(y1,...,y_b)
    pub fn evaluate_ts(&self, table: &TableData<F>, r: F) -> Vec<Vec<F>> {
        let data = LookupEvalDomain { table, r };
        let nrow = 2usize.pow(table.k);
        self.table_polys
            .iter()
            .map(|expr| expr.expand())
            .map(|poly| {
                (0..nrow)
                    .into_par_iter()
                    .map(|row| poly.eval(row, &data))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }
    /// calculate the coefficients {m_i} in the log derivative formula
    /// m_i = sum_j \xi(w_j=t_i) assuming {t_i} have no duplicates
    pub fn evaluate_m(&self, l: &[F], t: &[F]) -> Vec<F> {
        let mut m: Vec<F> = Vec::new();
        let mut processed_t = Vec::new();
        for t_i in t {
            if processed_t.contains(&t_i) {
                // If the current t_i has already been processed, push 0 to m
                m.push(F::ZERO);
            } else {
                let m_i = l.iter().filter(|l_j| *l_j == t_i).count() as u128;
                m.push(F::from_u128(m_i));
                processed_t.push(t_i);
            }
        }
        m
    }

    /// calculate the inverse in log derivative formula
    /// h_i := \frac{1}{l_i+r}
    /// g_i := \frac{m_i}{t_i+r}
    pub fn evaluate_h_g(&self, l: &[F], t: &[F], r: F, m: &[F]) -> (Vec<F>, Vec<F>) {
        let h = l
            .iter()
            .map(|&l_i| Option::from((l_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        let g = t
            .iter()
            .zip(m)
            .map(|(t_i, m_i)| *m_i * Option::from((*t_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        (h, g)
    }

    /// check whether the lookup argument is satisfied
    /// the remaining check L(x1,...,xa)=l and T(y1,...,ya)=t
    /// are carried in upper level check
    pub fn is_sat(&self, l: &[F], t: &[F], r: F) -> Result<(), String> {
        let m = self.evaluate_m(l, t);
        let (h, g) = self.evaluate_h_g(l, t, r, &m);
        // check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
        let c1 = l
            .iter()
            .zip(h.iter())
            .map(|(li, hi)| *hi * (*li + r) - F::ONE)
            .filter(|d| F::ZERO.ne(d))
            .count();

        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let c2 = t
            .iter()
            .zip(g.iter())
            .zip(m)
            .map(|((ti, gi), mi)| *gi * (*ti + r) - mi)
            .filter(|d| F::ZERO.ne(d))
            .count();

        // check sum_i h_i = sum_i g_i
        let sum = h
            .into_iter()
            .zip(g)
            .map(|(hi, gi)| hi - gi)
            .fold(F::ZERO, |acc, d| acc + d);
        let c3 = F::ZERO.ne(&sum);
        match (c1 == 0, c2 == 0, c3) {
            (true, true, true) => Ok(()),
            (false, _, _) => Err(format!("hi(li+r)-1=0 not satisfied on {} rows", c1,).to_string()),
            (true, false, _) => {
                Err(format!("gi(ti+r)-mi=0 not satisfied on {} rows", c2,).to_string())
            }
            (true, true, false) => Err("sum hi = sum gi not satisfied".to_string()),
        }
    }
}

/// Used for evaluate lookup relations L_i(x1,...,xn) defined in halo2 lookup arguments
pub struct LookupEvalDomain<'a, F: PrimeField> {
    pub(crate) table: &'a TableData<F>,
    pub(crate) r: F,
}
