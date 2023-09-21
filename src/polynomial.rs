use crate::table::TableData;
use crate::util::trim_leading_zeros;
use ff::PrimeField;
use halo2_proofs::plonk::Expression as PE;
use halo2_proofs::poly::Rotation;
use std::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    collections::{HashMap, HashSet},
    fmt,
    fmt::{Debug, Display},
    ops::{Add, Mul, Neg, Sub},
};

#[derive(Clone, Copy, Debug)]
pub struct Query {
    pub index: usize,
    pub rotation: Rotation,
}

#[derive(Clone, Debug)]
pub enum Expression<F> {
    Constant(F),
    Polynomial(Query),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),
}

impl<F: PrimeField> Display for Expression<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.visualize())
    }
}
impl<F: PrimeField> Expression<F> {
    // uniquely determined by (rotation, poly_index)
    pub fn poly_set(&self, set: &mut HashSet<(i32, usize)>) {
        match self {
            Expression::Constant(_) => (),
            Expression::Polynomial(poly) => {
                set.insert((poly.rotation.0, poly.index));
            }
            Expression::Negated(a) => a.poly_set(set),
            Expression::Sum(a, b) => {
                a.poly_set(set);
                b.poly_set(set);
            }
            Expression::Product(a, b) => {
                a.poly_set(set);
                b.poly_set(set);
            }
            Expression::Scaled(a, _) => a.poly_set(set),
        }
    }

    fn _expand(&self, index_to_poly: &Vec<(i32, usize)>) -> MultiPolynomial<F> {
        match self {
            Expression::Constant(c) => {
                let arity = index_to_poly.len();
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.clone(), *c, vec![0; arity])],
                }
            }
            Expression::Polynomial(poly) => {
                let arity = index_to_poly.len();
                let mut exponents = vec![0; arity];
                let index = index_to_poly
                    .iter()
                    .position(|&(a, b)| a == poly.rotation.0 && b == poly.index)
                    .unwrap();
                exponents[index] = 1;
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.clone(), F::ONE, exponents)],
                }
            }
            Expression::Negated(a) => {
                let a = a._expand(index_to_poly);
                -a
            }
            Expression::Sum(a, b) => {
                let a = a._expand(index_to_poly);
                let b = b._expand(index_to_poly);
                a + b
            }
            Expression::Product(a, b) => {
                let a = a._expand(index_to_poly);
                let b = b._expand(index_to_poly);
                a * b
            }
            Expression::Scaled(a, k) => {
                let a = a._expand(index_to_poly);
                a * *k
            }
        }
    }

    pub fn expand(&self) -> MultiPolynomial<F> {
        let mut set = HashSet::new();
        self.poly_set(&mut set);
        let mut index_to_poly: Vec<(i32, usize)> = set.into_iter().collect();
        index_to_poly.sort();
        self._expand(&index_to_poly)
    }

    pub fn fold_transform(&self, meta: (usize, usize, usize)) -> Self {
        match self {
            Expression::Constant(c) => Expression::Constant(*c),
            Expression::Polynomial(poly) => {
                if poly.index < meta.0 {
                    return Expression::Polynomial(*poly);
                }
                // u1, u2 is added
                let r = Expression::Polynomial(Query {
                    index: meta.0 + 2 * (meta.1 + meta.2 + 1),
                    rotation: Rotation(0),
                });
                let index_shift = meta.1 + meta.2 + 1;
                let y = Expression::Polynomial(Query {
                    index: poly.index + index_shift,
                    rotation: poly.rotation,
                });
                Expression::Polynomial(*poly) + r * y
            }
            Expression::Negated(a) => {
                let a = a.fold_transform(meta);
                -a
            }
            Expression::Sum(a, b) => {
                let a = a.fold_transform(meta);
                let b = b.fold_transform(meta);
                a + b
            }
            Expression::Product(a, b) => {
                let a = a.fold_transform(meta);
                let b = b.fold_transform(meta);
                a * b
            }
            Expression::Scaled(a, k) => {
                let a = a.fold_transform(meta);
                a * *k
            }
        }
    }

    fn visualize(&self) -> String {
        match self {
            Expression::Constant(c) => trim_leading_zeros(format!("{:?}", c)),
            Expression::Polynomial(poly) => {
                let rotation = match poly.rotation.0.cmp(&0) {
                    Ordering::Equal => "".to_owned(),
                    Ordering::Less => format!("[{}]", poly.rotation.0),
                    Ordering::Greater => format!("[+{}]", poly.rotation.0),
                };

                format!("Z_{}{}", poly.index, rotation)
            }
            Expression::Negated(a) => {
                let a = a.visualize();
                format!("(-{})", a)
            }
            Expression::Sum(a, b) => {
                let a = a.visualize();
                let b = b.visualize();
                format!("({} + {})", a, b)
            }
            Expression::Product(a, b) => {
                let a = a.visualize();
                let b = b.visualize();
                format!("({} * {})", a, b)
            }
            Expression::Scaled(a, k) => {
                let a = a.visualize();
                let k = trim_leading_zeros(format!("{:?}", k));
                format!("{} * {}", k, a)
            }
        }
    }

    // we need (num_fixed_columns, num_instance_columns) to recover
    pub fn from_halo2_expr(expr: &PE<F>, meta: (usize, usize)) -> Self {
        match expr {
            PE::Constant(c) => Expression::Constant(*c),
            PE::Fixed(query) => Expression::Polynomial(Query {
                index: query.column_index(),
                rotation: query.rotation(),
            }),
            PE::Instance(query) => Expression::Polynomial(Query {
                index: meta.0 + query.column_index(),
                rotation: query.rotation(),
            }),
            PE::Advice(query) => Expression::Polynomial(Query {
                index: meta.0 + meta.1 + query.column_index(),
                rotation: query.rotation(),
            }),
            PE::Negated(a) => {
                let a = Self::from_halo2_expr(a, meta);
                -a
            }
            PE::Sum(a, b) => {
                let a = Self::from_halo2_expr(a, meta);
                let b = Self::from_halo2_expr(b, meta);
                a + b
            }
            PE::Product(a, b) => {
                let a = Self::from_halo2_expr(a, meta);
                let b = Self::from_halo2_expr(b, meta);
                a * b
            }
            PE::Scaled(a, k) => {
                let a = Self::from_halo2_expr(a, meta);
                a * *k
            }
            _ => unimplemented!("not supported"),
        }
    }
}

impl<F: PrimeField> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self))
    }
}

impl<F: PrimeField> Mul<F> for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: F) -> Expression<F> {
        Expression::Scaled(Box::new(self), rhs)
    }
}

macro_rules! impl_expression_ops {
    ($trait:ident, $method:ident, $variant:ident, $rhs: ty, $rhs_expr: expr) => {
        impl<F: PrimeField> $trait for Expression<F> {
            type Output = Expression<F>;

            fn $method(self, rhs: $rhs) -> Self::Output {
                Expression::$variant(Box::new(self), Box::new($rhs_expr(rhs)))
            }
        }
    };
}

impl_expression_ops!(Add, add, Sum, Expression<F>, std::convert::identity);
impl_expression_ops!(Sub, sub, Sum, Expression<F>, Neg::neg);
impl_expression_ops!(Mul, mul, Product, Expression<F>, std::convert::identity);

/// Monomial: c_i*x_0*..*x_{n-1} with arity n
/// index_to_poly is mapping from i to (rotation, column_index)
/// poly_to_index is mapping from (rotation, column_index) to i \in [0,..,n-1]
#[derive(Clone)]
pub struct Monomial<F: PrimeField> {
    pub arity: usize,
    // poly: (rotation, column_index)
    pub index_to_poly: Vec<(i32, usize)>,
    // (rotation, column_index) -> index
    pub poly_to_index: HashMap<(i32, usize), usize>,
    pub coeff: F,
    pub exponents: Vec<usize>,
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
            let (rid, cid) = self.index_to_poly[i];
            let shift = match rid.cmp(&0) {
                Ordering::Equal => "".to_owned(),
                Ordering::Greater => format!("[+{rid}]"),
                Ordering::Less => format!("[{rid}]"),
            };

            if *exp == 1 {
                write!(f, "(Z_{}{})", cid, shift)?;
            } else {
                write!(f, "(Z_{}{}^{})", cid, shift, exp)?;
            }
        }
        write!(f, "")
    }
}

impl<F: PrimeField> Monomial<F> {
    pub fn new(index_to_poly: Vec<(i32, usize)>, coeff: F, exponents: Vec<usize>) -> Self {
        let arity = index_to_poly.len();
        assert!(arity == exponents.len());
        let mut poly_to_index: HashMap<(i32, usize), usize> = HashMap::new();
        for (i, key) in index_to_poly.iter().enumerate() {
            poly_to_index.insert(*key, i);
        }

        Self {
            arity,
            index_to_poly,
            poly_to_index,
            coeff,
            exponents,
        }
    }

    pub fn homogeneous(&self, degree: usize, u_index: usize) -> Self {
        let mut mono = self.clone();
        mono.arity += 1;
        mono.exponents.push(degree - self.degree());
        mono.index_to_poly.push((0, u_index));
        mono.poly_to_index.insert((0, u_index), mono.arity);
        mono
    }

    pub fn to_expression(&self) -> Expression<F> {
        let mut expr = Expression::Constant(F::ONE);
        for (i, exp) in self.exponents.iter().enumerate() {
            let (rot, idx) = self.index_to_poly[i];
            for _ in 0..(*exp) {
                let x0 = Expression::<F>::Polynomial(Query {
                    index: idx,
                    rotation: Rotation(rot),
                });
                expr = Expression::Product(Box::new(expr), Box::new(x0));
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

    pub fn eval(&self, row: usize, td: &TableData<F>, u: F) -> F {
        let num_fixed = td.fixed.len();
        let num_advice = td.advice.len();
        let vars: Vec<F> = (0..self.arity)
            .map(|i| {
                let (rot, col) = self.index_to_poly[i];
                let row1 = if (rot + row as i32) >= 0 {
                    rot as usize + row
                } else {
                    // TODO: check how halo2 handle
                    // (1): row+rot<0
                    // (2): row+rot>=2^K
                    td.fixed[0].len() - (-rot as usize) + row
                };
                if col < num_fixed {
                    td.fixed[col][row1].evaluate()
                } else if col < num_fixed + 1 {
                    // instance column is always 1
                    td.instance[row1]
                } else if col < num_fixed + 1 + num_advice {
                    td.advice[col - num_fixed - 1][row1].evaluate()
                } else {
                    // homogeneous term
                    u
                }
            })
            .collect();

        let res = vars
            .into_iter()
            .zip(self.exponents.iter())
            .map(|(x, exp)| x.pow([*exp as u64, 0, 0, 0]))
            .fold(F::ONE, |acc, v| acc * v);
        res * self.coeff
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

#[derive(Clone)]
pub struct MultiPolynomial<F: PrimeField> {
    pub arity: usize,
    pub monomials: Vec<Monomial<F>>,
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
                deg = monomial.degree()
            }
        }
        deg
    }

    pub fn homogeneous(&self, meta: (usize, usize, usize)) -> Self {
        let degree = self.degree();
        let u_index = meta.0 + meta.1 + meta.2;
        let monos = self
            .monomials
            .iter()
            .map(|f| f.homogeneous(degree, u_index))
            .collect();
        Self {
            arity: self.arity + 1,
            monomials: monos,
        }
    }

    pub fn to_expression(&self) -> Expression<F> {
        let mut expr = Expression::Constant(F::ZERO);
        for mono in self.monomials.iter() {
            expr = Expression::Sum(Box::new(expr), Box::new(mono.to_expression()));
        }
        expr
    }

    // p(X1,X2,...) -> p(X1+r*Y1,X2+r*Y2,...)
    // meta: size of |fixed_columns|instance_columns|advice_columns|
    pub fn fold_transform(&self, meta: (usize, usize, usize)) -> Self {
        self.homogeneous(meta)
            .to_expression()
            .fold_transform(meta)
            .expand()
    }

    // get coefficient of X^k, where X identified by (ratation, index) in 0..arity, k=degree
    pub fn coeff_of(&self, var: (i32, usize), degree: usize) -> Self {
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
            if self.monomials[idx] == self.monomials[idx - 1] {
                let size = reduced.len();
                reduced[size - 1].add(&self.monomials[idx]);
            } else {
                reduced.push(self.monomials[idx].clone());
            }
        }
        self.monomials = reduced;
    }

    // evaluate the multipoly
    pub fn eval(&self, row: usize, td: &TableData<F>, u: F) -> F {
        self.monomials
            .iter()
            .map(|mono| mono.eval(row, td, u))
            .fold(F::ZERO, |acc, x| acc + x)
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

#[cfg(test)]
mod tests {
    use super::*;
    use ff::PrimeField;
    // use pasta_curves::{Fp, pallas};
    use halo2curves::pasta::{pallas, Fp};

    #[test]
    fn test_expression() {
        let expr1: Expression<Fp> =
            Expression::Polynomial(Query {
                index: 0,
                rotation: Rotation(0),
            }) - Expression::Constant(pallas::Base::from_str_vartime("1").unwrap());
        let expr2: Expression<Fp> = Expression::Polynomial(Query {
            index: 0,
            rotation: Rotation(0),
        }) * pallas::Base::from(2);
        let expr = expr1.clone() * expr1 + expr2;
        assert_eq!(format!("{}", expr.expand()), "0x1 + (Z_0^2)");
    }

    #[test]
    fn test_homogeneous() {
        let expr1: Expression<Fp> =
            Expression::Polynomial(Query {
                index: 0,
                rotation: Rotation(0),
            }) + Expression::Constant(pallas::Base::from_str_vartime("1").unwrap());
        let expr2: Expression<Fp> = Expression::<Fp>::Polynomial(Query {
            index: 0,
            rotation: Rotation(0),
        }) * Expression::<Fp>::Polynomial(Query {
            index: 1,
            rotation: Rotation(0),
        });
        let expr3 = expr1.clone() + expr2.clone();
        assert_eq!(
            format!("{}", expr3.expand().homogeneous((0, 0, 2))),
            "(Z_2^2) + (Z_0)(Z_2) + (Z_0)(Z_1)"
        );
    }
}
