//! This mod implements the special soundness protocol for lookup arguments
//! using log derivative approach.
//!
//! Reference: Section 4.3 in [protostar](https://eprint.iacr.org/2023/620)

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::CurveAffine,
    plonk::{ConstraintSystem, Expression as PE},
    poly::Rotation,
};

use crate::{
    commitment::CommitmentKey,
    polynomial::{sparse::SparseMatrix, Expression, MultiPolynomial, Query},
};

/// Starting from vector lookup: {(a1,a2,...,ak)} \subset {(t1,t2,...,tk)}
/// where {ai} are expressions over columns (x1,...xa)
/// {ti} are expressions over columns (y1,...,yb)
///
/// We assume (y1,...,yb) are fixed columns
/// compress them into one multi-polynomial:
/// lookup_poly = L(x1,...,xa) = a1+a2*r+a3*r^2+...
/// table_poly = T(y1,...,yb) = t1+t2*r+t3*r^2+...
#[derive(Clone, PartialEq)]
pub struct Argument<F: PrimeField> {
    pub(crate) lookup_poly: MultiPolynomial<F>,
    pub(crate) table_poly: MultiPolynomial<F>,
}

/// lookup structure includes all the necessary information of folding scheme for lookup
#[derive(Clone, PartialEq)]
pub struct Structure<C: CurveAffine> {
    /// 2^k1 is the length of lookup vector [`Witness::l`]
    pub(crate) k1: usize,
    /// 2^k2 is the length of table vector [`Witness::t`]
    pub(crate) k2: usize,
    /// commitment of [`Witness::t`], we assume table t is constructed by fixed columns
    pub(crate) t_commitment: C,
    /// check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
    pub(crate) l_rel: MultiPolynomial<C::ScalarExt>,
    /// check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
    pub(crate) t_rel: MultiPolynomial<C::ScalarExt>,
    /// check sum_i h_i = sum_i g_i
    pub(crate) h_mat: SparseMatrix<C::ScalarExt>,
    pub(crate) g_mat: SparseMatrix<C::ScalarExt>,
}

pub struct Instance<C: CurveAffine> {
    // commitment of l\cup m
    pub(crate) l_m_commitment: C,
    // commitment of h\cup g
    pub(crate) h_g_commitment: C,
    pub(crate) r: C::ScalarExt,
}

/// multiplicity_vec = \vec{m_i}
#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    //  l_i = L(x1[i],...,xa[i])
    pub(crate) l: Vec<F>,
    // t: is used to calculate m, h, g; no need to fold
    pub(crate) t: Vec<F>,
    // multiplicity vector
    pub(crate) m: Vec<F>,
    pub(crate) h: Vec<F>,
    pub(crate) g: Vec<F>,
}

pub struct RelaxedInstance<C: CurveAffine> {
    // commitment of l\cup m
    pub(crate) l_m_commitment: C,
    // commitment of h\cup g
    pub(crate) h_g_commitment: C,
    // commitment of e_l\cup e_t
    pub(crate) E_commitment: C,
    // random challenge
    pub(crate) r: C::ScalarExt,
    // homogenous variable
    pub(crate) u: C::ScalarExt,
}

#[derive(Clone)]
pub struct RelaxedWitness<F: PrimeField> {
    // l: folded from multiple Witness.l
    pub(crate) l: Vec<F>,
    // m: folded from multiple Witness.m
    pub(crate) m: Vec<F>,
    // h: folded from multiple Witness.h
    pub(crate) h: Vec<F>,
    // g: folded from multiple Witness.g
    pub(crate) g: Vec<F>,
    // error vector of l_rel, length 2^k1
    pub(crate) e_l: Vec<F>,
    // error vector of t_rel, length 2^k2
    pub(crate) e_t: Vec<F>,
}

/// Used for evaluate lookup relation
pub struct LookupEvalDomain<'a, F: PrimeField> {
    pub(crate) W1: &'a Witness<F>,
    pub(crate) W2: &'a Witness<F>,
}

impl<F: PrimeField> Argument<F> {
    /// retrieve and compress vector of Lookup Arguments from constraint system
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
        let input_polys = cs
            .lookups()
            .iter()
            .map(|arg| compress_expression(arg.input_expressions()))
            .collect::<Vec<_>>();
        let table_polys = cs
            .lookups()
            .iter()
            .map(|arg| compress_expression(arg.table_expressions()))
            .collect::<Vec<_>>();

        input_polys
            .into_iter()
            .zip(table_polys)
            .map(|(lookup_poly, table_poly)| Self {
                lookup_poly,
                table_poly,
            })
            .collect::<Vec<_>>()
    }
}

impl<C: CurveAffine<ScalarExt = F>, F: PrimeField> Structure<C> {
    pub fn new(&self, k1: usize, k2: usize, t_vec: Vec<F>, ck: &CommitmentKey<C>) -> Self {
        let t_commitment = ck.commit(&t_vec[..]);

        let l = Expression::Polynomial(Query {
            index: 0,
            rotation: Rotation(0),
        });
        let t = Expression::Polynomial(Query {
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
        // check sum_i h_i = sum_i g_i, i.e. h_mat * h = g_mat * g
        let mut h_mat = Vec::new();
        let mut g_mat = Vec::new();
        let _ = (0..2_usize.pow(k1 as u32)).map(|i| h_mat.push((0, i, F::ONE)));
        let _ = (0..2_usize.pow(k2 as u32)).map(|i| g_mat.push((0, i, F::ONE)));

        Self {
            k1,
            k2,
            t_commitment,
            l_rel,
            t_rel,
            h_mat,
            g_mat,
        }
    }
}

impl<F: PrimeField> Witness<F> {
    /// calculate the coefficients {m_i} in the log derivative formula
    /// m_i = sum_j \xi(w_j=t_i) assuming {t_i} have no duplicates
    pub fn log_derivative_coeffs(&self) -> Vec<F> {
        let mut m: Vec<F> = Vec::new();
        let mut processed_t = Vec::new();
        for t_i in &self.t {
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
    pub fn calc_inverse_terms(&self, r: F, m: &[F]) -> (Vec<F>, Vec<F>) {
        let h = self
            .l
            .iter()
            .map(|&l_i| Option::from((l_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        let g = self
            .t
            .iter()
            .zip(m)
            .map(|(t_i, m_i)| *m_i * Option::from((*t_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        (h, g)
    }

    /// check whether the lookup argument is satisfied
    /// the remaining check L(x1,...,xa)=l and T(y1,...,ya)=t
    /// are carried in upper level check
    pub fn is_sat(&self, r: F) -> Result<(), String> {
        let m = self.log_derivative_coeffs();
        let (h, g) = self.calc_inverse_terms(r, &m);
        // check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
        let c1 = self
            .l
            .iter()
            .zip(h.iter())
            .map(|(li, hi)| *hi * (*li + r) - F::ONE)
            .filter(|d| F::ZERO.ne(d))
            .count();

        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let c2 = self
            .t
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
