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

use crate::{
    plonk::util::compress_expression,
    polynomial::{Expression, Query, OFFSET_PAD},
};

/// Lookup Argument
///
/// Starting from vector lookup:
/// {(a_1, a_2, ..., a_k)} subset of {(t_1, t_2, ..., t_k)}
/// where:
/// - a_i are expressions over columns (x_1, ..., x_a)
/// - t_i are expressions over columns (y_1, ..., y_b)
///
/// We assume (y_1,...,y_b) are fixed columns compress them
/// into one multi-polynomial:
/// - lookup_poly = L(x_1,...,x_a) = a_1 + a_2*r + a_3*r^2 + ...
/// - table_poly  = T(y_1,...,y_b) = t_1 + t_2*r + t_3*r^2 + ...
#[derive(Clone, PartialEq)]
pub struct Argument<F: PrimeField> {
    /// vector of the lookup expressions
    pub(crate) lookup_polys: Vec<Expression<F>>,
    /// vector of the table expressions
    pub(crate) table_polys: Vec<Expression<F>>,
    /// return true when maximum length of lookup vector or table vector greater than 1
    pub(crate) require_challenge: bool,
    /// Check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
    /// same for every lookup
    pub(crate) log_derivative_lhs: Expression<F>,
    /// Check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
    /// same for every lookup
    pub(crate) log_derivative_rhs: Expression<F>,
}

impl<F: PrimeField> Argument<F> {
    /// Compresses a vector of Lookup Arguments from a constraint system into a single multi-polynomial.
    pub fn compress_from(cs: &ConstraintSystem<F>) -> Option<Self> {
        let max_lookup_len = cs
            .lookups()
            .iter()
            .map(|arg| arg.input_expressions().len())
            .max()
            .unwrap_or(0);
        let max_table_len = cs
            .lookups()
            .iter()
            .map(|arg| arg.table_expressions().len())
            .max()
            .unwrap_or(0);
        let max_len = max_lookup_len.max(max_table_len);
        if max_len == 0 {
            return None;
        }

        let require_challenge = max_len > 1;

        // suppose we have n polynomial expression: p_1,p_2,...,p_n
        // we combined them together as one: combined_poly = p_1*y^{n-1}+p_2*y^{n-2}+...+p_n
        let lookup_polys = cs
            .lookups()
            .iter()
            .map(|arg| {
                compress_expression(
                    &arg.input_expressions()[..],
                    cs.num_selectors(),
                    cs.num_fixed_columns(),
                    OFFSET_PAD,
                    0,
                )
            })
            .collect::<Vec<_>>();
        let table_polys = cs
            .lookups()
            .iter()
            .map(|arg| {
                compress_expression(
                    &arg.table_expressions()[..],
                    cs.num_selectors(),
                    cs.num_fixed_columns(),
                    OFFSET_PAD,
                    0,
                )
            })
            .collect::<Vec<_>>();
        let (log_derivative_lhs, log_derivative_rhs) = Self::log_derivative_exprs();

        Some(Self {
            lookup_polys,
            table_polys,
            require_challenge,
            log_derivative_lhs,
            log_derivative_rhs,
        })
    }

    pub fn log_derivative_exprs() -> (Expression<F>, Expression<F>) {
        let t = Expression::Polynomial(Query {
            index: 0,
            rotation: Rotation(0),
        });
        let l = Expression::Polynomial(Query {
            index: 1,
            rotation: Rotation(0),
        });
        let m = Expression::Polynomial(Query {
            index: 2,
            rotation: Rotation(0),
        });
        let r = Expression::Polynomial(Query {
            index: 3,
            rotation: Rotation(0),
        });
        let h = Expression::Polynomial(Query {
            index: 4,
            rotation: Rotation(0),
        });
        let g = Expression::Polynomial(Query {
            index: 5,
            rotation: Rotation(0),
        });
        // check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
        let lhs_rel = h * (l + r.clone()) - Expression::Constant(F::ONE);
        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let rhs_rel = g * (t + r) - m;
        (lhs_rel, rhs_rel)
    }

    /// calculate the coefficients {m_i} in the log derivative formula
    /// m_i = sum_j \xi(w_j=t_i) assuming {t_i} have no duplicates
    pub fn log_derivative_coeffs(&self, l: &[F], t: &[F]) -> Vec<F> {
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
    pub fn calc_inverse_terms(&self, l: &[F], t: &[F], r: F, m: &[F]) -> (Vec<F>, Vec<F>) {
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
        let m = self.log_derivative_coeffs(l, t);
        let (h, g) = self.calc_inverse_terms(l, t, r, &m);
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
