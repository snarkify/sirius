use std::{
    fmt::{self, Display},
    ops::{Add, Mul, Neg},
};

use ff::PrimeField;
use serde::Serialize;

use super::{
    expression::{ColumnIndex, Expression},
    monomial::Monomial,
};

#[derive(Clone, PartialEq, Serialize, Default)]
pub struct MultiPolynomial<F: PrimeField> {
    pub(crate) arity: usize,
    pub(crate) monomials: Vec<Monomial<F>>,
}

impl<F: PrimeField> Display for MultiPolynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut non_empty_monomials_count = 0;
        for monomial in &self.monomials {
            let formatted_monomial = format!("{}", monomial);
            if !formatted_monomial.is_empty() {
                if non_empty_monomials_count > 0 {
                    write!(f, " + ")?;
                }
                write!(f, "{}", formatted_monomial)?;
                non_empty_monomials_count += 1;
            }
        }
        Ok(())
    }
}

impl<F: PrimeField> MultiPolynomial<F> {
    pub fn new(arity: usize) -> Self {
        Self {
            arity,
            monomials: vec![],
        }
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn degree(&self) -> usize {
        let mut deg = 0;
        for monomial in self.monomials.iter() {
            if deg < monomial.degree() {
                deg = monomial.degree();
            }
        }
        deg
    }

    /// offset = num_fixed+num_selector, offset of variables to be folded
    pub fn degree_for_folding(&self, offset: usize) -> usize {
        let mut deg = 0;
        for monomial in self.monomials.iter() {
            if deg < monomial.degree_for_folding(offset) {
                deg = monomial.degree_for_folding(offset)
            }
        }
        deg
    }

    // when make polynomial homogeneous, we need specify the index of u
    pub fn homogeneous(&self, offset: usize) -> Self {
        let u_index = self.num_challenges();
        let degree = self.degree_for_folding(offset);
        let monos = self
            .monomials
            .iter()
            .map(|f| f.homogeneous(degree, offset, u_index))
            .collect();
        Self {
            arity: self.arity + 1,
            monomials: monos,
        }
    }

    pub fn num_challenges(&self) -> usize {
        self.to_expression().num_challenges()
    }

    pub fn to_expression(&self) -> Expression<F> {
        let mut expr = Expression::Constant(F::ZERO);
        for mono in self.monomials.iter() {
            expr = Expression::Sum(Box::new(expr), Box::new(mono.to_expression()));
        }
        expr
    }

    // fold_transform will (1) first homogeneous the polynomial
    // p(f_1,...,f_m,x_1,...,x_n) -> p'(f_1,...,f_m,x_1,...,x_n,u)
    // (2) fold variable x_i while keep variable f_i unchanged
    // p' -> p'(f_1,...,f_m, x_1+r*y_1,x_2+r*y_2,...,x_n+r*y_n)
    // mm = num_fixed + num_selectors, nn = num_advice + 5*num_lookup
    pub fn fold_transform(&self, mm: usize, nn: usize) -> Self {
        self.homogeneous(mm)
            .to_expression()
            .fold_transform(mm, nn)
            .expand()
    }

    // get coefficient of X^k, where X identified by (ratation, index, var_type) in 0..arity, k=degree
    pub fn coeff_of(&self, var: ColumnIndex, degree: usize) -> Self {
        assert!(!self.monomials.is_empty());
        assert!(self.monomials[0].poly_to_index.contains_key(&var));

        let index = self.monomials[0].poly_to_index.get(&var).unwrap();
        let mut index_to_poly = self.monomials[0].index_to_poly.clone();
        index_to_poly.remove(*index);

        let mut poly = Self::new(self.arity - 1);

        for mono in self.monomials.iter() {
            if mono.exponents[*index] == degree {
                let mut exponents = mono.exponents.clone();
                exponents.remove(*index);
                let tmp = Monomial::new(index_to_poly.clone(), mono.coeff, exponents);
                poly.monomials.push(tmp);
            }
        }
        poly
    }

    pub fn reduce(&mut self) {
        if self.monomials.len() <= 1 {
            return;
        }
        self.monomials.sort();
        let mut reduced: Vec<Monomial<F>> = Vec::new();
        let mut idx: usize = 0;
        reduced.push(self.monomials[idx].clone());
        loop {
            idx += 1;
            if idx >= self.monomials.len() {
                break;
            }
            if self.monomials[idx].coeff == F::ZERO {
                continue;
            } else if self.monomials[idx] == reduced[reduced.len() - 1] {
                let size = reduced.len();
                reduced[size - 1].add(&self.monomials[idx]);
            } else {
                reduced.push(self.monomials[idx].clone());
            }
        }
        self.monomials = reduced;
    }
}

impl<F: PrimeField> Neg for MultiPolynomial<F> {
    type Output = MultiPolynomial<F>;
    fn neg(self) -> Self::Output {
        let mut monomials = vec![];
        for monomial in self.monomials.iter() {
            let mut tmp = monomial.clone();
            tmp.coeff = monomial.coeff.neg();
            monomials.push(tmp);
        }

        MultiPolynomial {
            arity: self.arity(),
            monomials,
        }
    }
}

impl<F: PrimeField> Add for MultiPolynomial<F> {
    type Output = MultiPolynomial<F>;
    fn add(self, rhs: MultiPolynomial<F>) -> Self::Output {
        assert!(self.arity() == rhs.arity());
        let mut merged = self.monomials.clone();
        merged.extend(rhs.monomials.clone());
        let mut res = MultiPolynomial {
            arity: self.arity(),
            monomials: merged,
        };
        res.reduce();
        res
    }
}

impl<F: PrimeField> Mul for MultiPolynomial<F> {
    type Output = MultiPolynomial<F>;
    fn mul(self, rhs: MultiPolynomial<F>) -> Self::Output {
        assert!(self.arity() == rhs.arity());
        let mut merged = vec![];
        for x in self.monomials.iter() {
            for y in rhs.monomials.iter() {
                let z = x.mul(y);
                merged.push(z);
            }
        }
        let mut res = MultiPolynomial {
            arity: self.arity(),
            monomials: merged,
        };
        res.reduce();
        res
    }
}

impl<F: PrimeField> Mul<F> for MultiPolynomial<F> {
    type Output = MultiPolynomial<F>;
    fn mul(self, rhs: F) -> Self::Output {
        let mut merged = vec![];
        for x in self.monomials.iter() {
            let z = x.scalar_mul(rhs);
            merged.push(z);
        }
        MultiPolynomial {
            arity: self.arity(),
            monomials: merged,
        }
    }
}
