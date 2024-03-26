use std::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    collections::HashMap,
    fmt,
    fmt::{Debug, Display},
};

use ff::PrimeField;
use halo2_proofs::poly::Rotation;
use serde::Serialize;

use crate::util::trim_leading_zeros;

use super::expression::{ColumnIndex, Expression, Query};

/// Monomial: c_i*x_0^d_0*..*x_{n-1}^d_{n-1} with arity n
/// index_to_poly is mapping from i to (rotation, column_index, type)
/// poly_to_index is mapping from (rotation, column_index, type) to i \in [0,..,n-1]
/// type has value either CHALLENGE_TYPE or POLYNOMIAL_TYPE
#[derive(Debug, Clone, Serialize)]
pub struct Monomial<F: PrimeField> {
    pub(crate) arity: usize,
    // poly or challenge: (rotation, column_index, type)
    pub(crate) index_to_poly: Vec<ColumnIndex>,
    // (rotation, column_index, var_type) -> index
    // when type = CHALLENGE_TYPE as a challenge, we always set rotation = 0
    pub(crate) poly_to_index: HashMap<ColumnIndex, usize>,
    pub(crate) coeff: F,
    pub(crate) exponents: Vec<usize>,
}

impl<F: PrimeField> Display for Monomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.coeff == F::ZERO {
            return write!(f, "");
        }
        if self.coeff != F::ONE || self.degree() == 0 {
            let coeff_str = trim_leading_zeros(format!("{:?}", self.coeff));
            write!(f, "{}", coeff_str)?;
        }
        for (i, exp) in self.exponents.iter().enumerate() {
            if *exp == 0 {
                continue;
            }

            match self.index_to_poly[i] {
                ColumnIndex::Challenge { column_index } => {
                    if *exp == 1 {
                        write!(f, "(r_{column_index})")?;
                    } else {
                        write!(f, "(r_{column_index}^{exp})")?;
                    }
                }
                ColumnIndex::Polynominal {
                    rotation,
                    column_index,
                } => {
                    let shift = match rotation.cmp(&0) {
                        Ordering::Equal => "".to_owned(),
                        Ordering::Greater => format!("[+{rotation}]"),
                        Ordering::Less => format!("[{rotation}]"),
                    };

                    if *exp == 1 {
                        write!(f, "(Z_{column_index}{shift})")?;
                    } else {
                        write!(f, "(Z_{column_index}{shift}^{exp})")?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl<F: PrimeField> Monomial<F> {
    pub fn new(index_to_poly: Vec<ColumnIndex>, coeff: F, exponents: Vec<usize>) -> Self {
        let arity = index_to_poly.len();
        assert!(arity == exponents.len());

        let mut poly_to_index = HashMap::new();
        for (i, key) in index_to_poly.iter().enumerate() {
            poly_to_index.insert(key.clone(), i);
        }

        Self {
            arity,
            index_to_poly,
            poly_to_index,
            coeff,
            exponents,
        }
    }

    /// offset = num_selector+num_fixed, equals number of variables that are not folded,
    pub fn homogeneous(&self, degree: usize, offset: usize, u_index: usize) -> Self {
        let mut mono = self.clone();
        mono.arity += 1;
        mono.exponents
            .push(degree - self.degree_for_folding(offset));
        mono.index_to_poly.push(ColumnIndex::Challenge {
            column_index: u_index,
        });
        mono.poly_to_index.insert(
            ColumnIndex::Challenge {
                column_index: u_index,
            },
            mono.arity,
        );
        mono
    }

    pub fn to_expression(&self) -> Expression<F> {
        let mut expr = Expression::Constant(self.coeff);
        for (i, exp) in self.exponents.iter().enumerate() {
            match self.index_to_poly[i] {
                ColumnIndex::Polynominal {
                    rotation,
                    column_index,
                } => {
                    for _ in 0..(*exp) {
                        let x0 = Expression::<F>::Polynomial(Query {
                            index: column_index,
                            rotation: Rotation(rotation),
                        });
                        expr = Expression::Product(Box::new(expr), Box::new(x0));
                    }
                }
                ColumnIndex::Challenge { column_index } => {
                    for _ in 0..(*exp) {
                        let r = Expression::<F>::Challenge(column_index);
                        expr = Expression::Product(Box::new(expr), Box::new(r));
                    }
                }
            }
        }
        expr
    }

    pub fn is_same_class(&self, other: &Self) -> bool {
        if self.arity != other.arity {
            return false;
        }
        let matching = self
            .index_to_poly
            .iter()
            .zip(&other.index_to_poly)
            .filter(|&(a, b)| a == b)
            .count();
        matching == self.arity
    }

    // this is used for folding, each variable has index
    // if the index < offset=num_selector+num_fixed, it will be treated as "const"
    // i.e. not folded
    pub fn degree_for_folding(&self, offset: usize) -> usize {
        self.exponents
            .iter()
            .zip(self.index_to_poly.iter())
            .filter_map(|(exp, indexes)| match indexes {
                ColumnIndex::Polynominal { column_index, .. } if column_index >= &offset => {
                    Some(exp)
                }
                ColumnIndex::Challenge { .. } => Some(exp),
                _other => None,
            })
            .sum()
    }

    pub fn degree(&self) -> usize {
        let mut deg = 0;
        for exp in self.exponents.iter() {
            deg += *exp;
        }
        deg
    }

    pub fn mul(&self, other: &Self) -> Self {
        assert!(self.is_same_class(other));
        let mut exponents = vec![];
        for (a, b) in self.exponents.iter().zip(other.exponents.iter()) {
            exponents.push(*a + *b);
        }
        Self {
            arity: self.arity,
            index_to_poly: self.index_to_poly.clone(),
            poly_to_index: self.poly_to_index.clone(),
            coeff: self.coeff * other.coeff,
            exponents,
        }
    }

    pub fn scalar_mul(&self, scalar: F) -> Self {
        Self {
            arity: self.arity,
            index_to_poly: self.index_to_poly.clone(),
            poly_to_index: self.poly_to_index.clone(),
            coeff: self.coeff * scalar,
            exponents: self.exponents.clone(),
        }
    }

    // requires they have same base
    pub fn add(&mut self, other: &Self) {
        assert!(self == other);
        self.coeff += other.coeff;
    }
}

impl<F: PrimeField> PartialEq for Monomial<F> {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.is_same_class(other));
        for (a, b) in self.exponents.iter().zip(other.exponents.iter()) {
            if *a != *b {
                return false;
            }
        }
        true
    }
}

impl<F: PrimeField> Eq for Monomial<F> {}

impl<F: PrimeField> PartialOrd for Monomial<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: PrimeField> Ord for Monomial<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        assert!(self.is_same_class(other));

        for (a, b) in self.exponents.iter().zip(other.exponents.iter()).rev() {
            match a.cmp(b) {
                Ordering::Equal => continue,
                order => {
                    return order;
                }
            }
        }
        Ordering::Equal
    }
}
