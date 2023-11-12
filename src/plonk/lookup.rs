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
//! ## Key Components
//!
//! - [`Argument`]: Represents the lookup argument with compressed polynomials
//!   for both the lookup vector and the table vector.
//! - [`Structure`]: Contains all the necessary information for the folding
//!   scheme of the lookup argument, including commitments and relations.
//! - [`Instance`]: Holds commitments for the lookup and table vectors, along
//!   with a random challenge.
//! - [`Witness`]: Represents the actual values for the lookup and table vectors,
//!   along with multiplicity and inverse terms.
//! - [`RelaxedInstance`]: A variant of `Instance` that includes additional
//!   commitments for error terms.
//! - [`RelaxedWitness`]: A variant of `Witness` that includes error vectors
//!   for relaxed instances.
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
use halo2_proofs::{
    arithmetic::CurveAffine,
    plonk::{ConstraintSystem, Expression as PE},
    poly::Rotation,
};

use crate::{
    commitment::CommitmentKey,
    polynomial::{Expression, MultiPolynomial, Query},
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
    /// Multi-polynomial representation of the lookup vector.
    pub(crate) lookup_poly: MultiPolynomial<F>,
    /// Multi-polynomial representation of the table vector.
    pub(crate) table_poly: MultiPolynomial<F>,
}

/// Lookup structure includes all the necessary information of folding scheme for lookup
///
/// This includes the necessary components for the folding scheme of lookup arguments,
/// such as commitments and relations. It is a key part of the IVC scheme,
/// allowing for efficient verification of lookup arguments.
#[derive(Clone, PartialEq)]
pub struct Structure<C: CurveAffine> {
    /// 2^k1 is the length of lookup vector [`Witness::l`]
    pub(crate) k1: usize,
    /// 2^k2 is the length of table vector [`Witness::t`]
    pub(crate) k2: usize,
    /// Table vector, used in the calculation of `m`, `h`, and `g`.
    pub(crate) t: Vec<C::ScalarExt>,
    /// Commitment of table vector, we assume table t is constructed by fixed columns
    pub(crate) t_commitment: C,
    /// Check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
    pub(crate) l_rel: MultiPolynomial<C::ScalarExt>,
    /// Check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
    pub(crate) t_rel: MultiPolynomial<C::ScalarExt>,
}

/// Represents an instance of a lookup argument
///
/// This structure holds commitments and a random challenge, which are essential
/// for the evaluation and verification of lookup arguments in the IVC scheme
pub struct Instance<C: CurveAffine> {
    /// Commitment to the concatenation of witness vectors [`Witness::l`] and [`Witness::m`].
    pub(crate) l_m_commitment: C,
    /// Commitment to the concatenation of witness vectors [`Witness::h`] and [`Witness::g`].
    pub(crate) h_g_commitment: C,
    /// Random challenge used in the verification process.
    pub(crate) r: C::ScalarExt,
}

/// Contains the witness vectors for a lookup argument
///
/// The witness vectors are crucial for constructing and verifying lookup arguments.
/// They are used to calculate multiplicity vectors and inverse terms as part of the
/// IVC scheme's verification process.
#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    /// Lookup vector, used to calculate the multiplicity vector.
    ///
    /// l_i = L(x1[i],...,xa[i])
    pub(crate) l: Vec<F>,

    /// Multiplicity vector, representing the coefficients in the log
    /// derivative formula.
    pub(crate) m: Vec<F>,

    /// Inverse terms for the lookup vector.
    /// This vector contains the inverse of each element in the lookup
    /// vector plus a random challenge `r`.
    pub(crate) h: Vec<F>,

    /// Inverse terms for the table vector.
    /// This vector contains the product of the multiplicity vector and the inverse
    /// of each element in the table vector plus a random challenge `r`.
    pub(crate) g: Vec<F>,
}

/// Represents a relaxed instance of a lookup argument
///
/// This structure is used when a more flexible approach to lookup argument verification is needed.
/// It includes additional commitments and variables that allow for a relaxed verification process,
/// which can be beneficial in certain scenarios within the IVC scheme.
pub struct RelaxedInstance<C: CurveAffine> {
    /// Commitment to the concatenation of witness vectors [`Witness::l`] and [`Witness::m`].
    pub(crate) l_m_commitment: C,
    /// Commitment to the concatenation of witness vectors [`Witness::h`] and [`Witness::g`].
    pub(crate) h_g_commitment: C,
    /// Commitment to the error vectors `e_l` and `e_t`.
    pub(crate) E_commitment: C,
    /// Random challenge used in the verification process
    pub(crate) r: C::ScalarExt,
    /// slack variable to make polynomial relation homogenous
    pub(crate) u: C::ScalarExt,
}

/// Contains the relaxed witness vectors for a lookup argument.
///
/// Similar to the standard witness structure, but includes error vectors for a more flexible
/// verification process.
#[derive(Clone)]
pub struct RelaxedWitness<F: PrimeField> {
    /// Folded from multiple [`Witness::l`]
    pub(crate) l: Vec<F>,
    /// Folded from multiple [`Witness::m`]
    pub(crate) m: Vec<F>,
    /// Folded from multiple [`Witness::h`]
    pub(crate) h: Vec<F>,
    /// g: folded from multiple [`Witness::g`]
    pub(crate) g: Vec<F>,
    /// Error vector of `l_rel`, length 2^k1
    pub(crate) e_l: Vec<F>,
    /// Error vector of `t_rel`, length 2^k2
    pub(crate) e_t: Vec<F>,
}

/// Provides a domain for evaluating lookup relations
///
/// This structure is used to hold references to witness vectors for the purpose of evaluating
/// lookup relations. It is a utility structure that facilitates the computation of expressions
/// within the IVC scheme.
pub struct LookupEvalDomain<'a, F: PrimeField> {
    /// Reference to the first witness vector.
    /// This is used to evaluate the lookup relation for the first set of witness values.
    pub(crate) W1: &'a Witness<F>,
    /// Reference to the second witness vector.
    /// This is used to evaluate the lookup relation for the second set of witness values.
    pub(crate) W2: &'a Witness<F>,
}

impl<F: PrimeField> Argument<F> {
    /// Compresses a vector of Lookup Arguments from a constraint system into a single multi-polynomial.
    ///
    /// This function is crucial for the IVC scheme as it reduces the complexity of the lookup argument,
    /// making it more efficient to verify.
    ///
    /// TODO #39:  halo2 assumes lookup relation to be true over all rows, in reality we may only
    /// lookup a few items. need find a way to remove padded rows for lookup_vec
    pub fn compress_from(cs: &ConstraintSystem<F>) -> Vec<Self> {
        // we use the same challenge y for combining custom gates and multiple lookup arguments
        // need first commit all witness before generating y
        let y = Expression::Polynomial(Query {
            index: cs.num_selectors() + cs.num_fixed_columns() + cs.num_advice_columns(),
            rotation: Rotation(0),
        });
        // suppose we have n polynomial expression: p_1,p_2,...,p_n
        // we combined them together as one: combined_poly = p_1*y^{n-1}+p_2*y^{n-2}+...+p_n
        let compress_expression = |exprs: &[PE<F>]| -> MultiPolynomial<F> {
            exprs
                .iter()
                .map(|expr| {
                    Expression::from_halo2_expr(expr, cs.num_selectors(), cs.num_fixed_columns())
                })
                .fold(Expression::Constant(F::ZERO), |acc, expr| {
                    Expression::Sum(
                        Box::new(expr),
                        Box::new(Expression::Product(Box::new(acc), Box::new(y.clone()))),
                    )
                })
                .expand()
        };

        cs.lookups()
            .iter()
            .map(|arg| Self {
                lookup_poly: compress_expression(arg.input_expressions()),
                table_poly: compress_expression(arg.table_expressions()),
            })
            .collect()
    }
}

impl<C: CurveAffine<ScalarExt = F>, F: PrimeField> Structure<C> {
    /// Constructs a new `Structure` instance for managing lookup arguments.
    /// This function initializes the structure with the necessary components for the folding scheme.
    ///
    /// # Arguments
    ///
    /// * `k1` - The power of 2 that determines the length of the lookup vector.
    /// * `k2` - The power of 2 that determines the length of the table vector.
    /// * `t_vec` - The table vector used to calculate the commitment.
    /// * `ck` - A reference to the commitment key used for generating cryptographic commitments.
    ///
    /// # Returns
    ///
    /// A new instance of `Structure` with initialized fields.
    pub fn new(&self, k1: usize, k2: usize, t_vec: Vec<F>, ck: &CommitmentKey<C>) -> Self {
        let t_commitment = ck.commit(&t_vec[..]);

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
        let l_rel = (h * (l + r.clone()) - Expression::Constant(F::ONE)).expand();
        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let t_rel = (g * (t + r) - m).expand();
        Self {
            k1,
            k2,
            t: t_vec,
            t_commitment,
            l_rel,
            t_rel,
        }
    }
}

impl<F: PrimeField> Witness<F> {
    /// calculate the coefficients {m_i} in the log derivative formula
    /// m_i = sum_j \xi(w_j=t_i) assuming {t_i} have no duplicates
    pub fn log_derivative_coeffs<C: CurveAffine<ScalarExt = F>>(
        &self,
        ss: &Structure<C>,
    ) -> Vec<F> {
        let mut m: Vec<F> = Vec::new();
        let mut processed_t = Vec::new();
        for t_i in &ss.t {
            if processed_t.contains(&t_i) {
                // If the current t_i has already been processed, push 0 to m
                m.push(F::ZERO);
            } else {
                let m_i = self.l.iter().filter(|l_j| *l_j == t_i).count() as u128;
                m.push(F::from_u128(m_i));
                processed_t.push(t_i);
            }
        }
        m
    }

    /// calculate the inverse in log derivative formula
    /// h_i := \frac{1}{l_i+r}
    /// g_i := \frac{m_i}{t_i+r}
    pub fn calc_inverse_terms<C: CurveAffine<ScalarExt = F>>(
        &self,
        ss: &Structure<C>,
        r: F,
        m: &[F],
    ) -> (Vec<F>, Vec<F>) {
        let h = self
            .l
            .iter()
            .map(|&l_i| Option::from((l_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        let g =
            ss.t.iter()
                .zip(m)
                .map(|(t_i, m_i)| *m_i * Option::from((*t_i + r).invert()).unwrap_or(F::ZERO))
                .collect::<Vec<F>>();
        (h, g)
    }

    /// check whether the lookup argument is satisfied
    /// the remaining check L(x1,...,xa)=l and T(y1,...,ya)=t
    /// are carried in upper level check
    pub fn is_sat<C: CurveAffine<ScalarExt = F>>(
        &self,
        ss: &Structure<C>,
        r: F,
    ) -> Result<(), String> {
        let m = self.log_derivative_coeffs(ss);
        let (h, g) = self.calc_inverse_terms(ss, r, &m);
        // check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
        let c1 = self
            .l
            .iter()
            .zip(h.iter())
            .map(|(li, hi)| *hi * (*li + r) - F::ONE)
            .filter(|d| F::ZERO.ne(d))
            .count();

        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let c2 =
            ss.t.iter()
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
