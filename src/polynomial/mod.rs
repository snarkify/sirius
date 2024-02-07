use std::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    collections::{BTreeSet, HashMap, HashSet},
    fmt,
    fmt::{Debug, Display},
    ops::{Add, Mul, Neg, Sub},
};

use ff::PrimeField;
use halo2_proofs::{plonk::Expression as PE, poly::Rotation};
use log::*;
use rayon::prelude::*;
use serde::Serialize;

use crate::util::trim_leading_zeros;

pub mod sparse;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum ColumnIndex {
    Challenge { column_index: usize },
    Polynominal { rotation: i32, column_index: usize },
}

impl PartialOrd for ColumnIndex {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ColumnIndex {
    fn cmp(&self, other: &Self) -> Ordering {
        let to_tuple = |s: &Self| match s {
            Self::Polynominal {
                rotation,
                column_index,
            } => (*rotation, *column_index, 0),
            Self::Challenge { column_index } => (0, *column_index, 1),
        };

        to_tuple(self).cmp(&to_tuple(other))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub struct Query {
    pub index: usize,
    #[serde(serialize_with = "serialize_rotation")]
    pub rotation: Rotation,
}

fn serialize_rotation<S: serde::ser::Serializer>(
    v: &Rotation,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    v.0.serialize(serializer)
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub enum Expression<F> {
    Constant(F),
    Polynomial(Query),
    Challenge(usize),
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
    // uniquely determined by (rotation, index, var_type)
    pub fn poly_set(&self, set: &mut BTreeSet<ColumnIndex>) {
        match self {
            Expression::Constant(_) => (),
            Expression::Polynomial(poly) => {
                set.insert(ColumnIndex::Polynominal {
                    rotation: poly.rotation.0,
                    column_index: poly.index,
                });
            }
            Expression::Challenge(index) => {
                set.insert(ColumnIndex::Challenge {
                    column_index: *index,
                });
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

    // return the number of challenges in expression
    pub fn num_challenges(&self) -> usize {
        let mut set = HashSet::new();
        self.collect_challenges(&mut set);
        set.len()
    }

    fn collect_challenges(&self, set: &mut HashSet<ColumnIndex>) {
        match self {
            Expression::Constant(_) => (),
            Expression::Polynomial(_) => (),
            Expression::Challenge(index) => {
                set.insert(ColumnIndex::Challenge {
                    column_index: *index,
                });
            }
            Expression::Negated(a) => a.collect_challenges(set),
            Expression::Sum(a, b) => {
                a.collect_challenges(set);
                b.collect_challenges(set);
            }
            Expression::Product(a, b) => {
                a.collect_challenges(set);
                b.collect_challenges(set);
            }
            Expression::Scaled(a, _) => a.collect_challenges(set),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        constant: &impl Fn(F) -> T,
        poly: &impl Fn(Query) -> T,
        challenge: &impl Fn(usize) -> T,
        negated: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
        scaled: &impl Fn(T, F) -> T,
    ) -> T {
        let evaluate = |expr: &Expression<F>| {
            expr.evaluate(constant, poly, challenge, negated, sum, product, scaled)
        };
        match self {
            Expression::Constant(scalar) => constant(*scalar),
            Expression::Polynomial(query) => poly(*query),
            Expression::Challenge(usize) => challenge(*usize),
            Expression::Negated(a) => {
                let a = evaluate(a);
                negated(a)
            }
            Expression::Sum(a, b) => {
                let a = evaluate(a);
                let b = evaluate(b);
                sum(a, b)
            }
            Expression::Product(a, b) => {
                let a = evaluate(a);
                let b = evaluate(b);
                product(a, b)
            }
            Expression::Scaled(a, scalar) => {
                let a = evaluate(a);
                scaled(a, *scalar)
            }
        }
    }

    /// index_to_poly is mapping from i to (rotation, column_index, type), see [`Monomial`]
    fn _expand(&self, index_to_poly: &[ColumnIndex]) -> MultiPolynomial<F> {
        self.evaluate(
            &|c| {
                let arity = index_to_poly.len();
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.to_vec(), c, vec![0; arity])],
                }
            },
            &|poly| {
                let arity = index_to_poly.len();
                let mut exponents = vec![0; arity];

                let index = index_to_poly
                    .iter()
                    .position(|indexes| {
                        indexes.eq(&ColumnIndex::Polynominal {
                            rotation: poly.rotation.0,
                            column_index: poly.index,
                        })
                    })
                    .unwrap();
                exponents[index] = 1;
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.to_vec(), F::ONE, exponents)],
                }
            },
            &|challenge_index| {
                let arity = index_to_poly.len();
                let mut exponents = vec![0; arity];
                let index = index_to_poly
                    .iter()
                    .position(|indexes| {
                        indexes.eq(&ColumnIndex::Challenge {
                            column_index: challenge_index,
                        })
                    })
                    .unwrap();
                exponents[index] = 1;
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.to_vec(), F::ONE, exponents)],
                }
            },
            &|a| -a,
            &|a, b| a + b,
            &|a, b| a * b,
            &|a, k| a * k,
        )
    }

    pub fn expand(&self) -> MultiPolynomial<F> {
        let mut set = BTreeSet::new();
        self.poly_set(&mut set);
        let index_to_poly = set.into_iter().collect::<Box<[_]>>();
        self._expand(&index_to_poly)
    }

    // fold_transform will fold a polynomial expression P(f_1,...f_m, x_1,...,x_n)
    // and output P(f_1,...,f_m, x_1+r*y_1,...,x_n+r*y_n)
    // here mm = num_fixed+num_selectors
    // nn = num_advice
    fn fold_transform(&self, mm: usize, nn: usize) -> Self {
        let num_challenges = self.num_challenges();
        let r = Expression::Challenge(2 * num_challenges);
        self.evaluate(
            &|c| Expression::Constant(c),
            &|poly| {
                if poly.index < mm {
                    return Expression::Polynomial(poly);
                }
                let y = Expression::Polynomial(Query {
                    index: poly.index + nn,
                    rotation: poly.rotation,
                });
                // fold variable x_i -> x_i + r * y_i
                Expression::Polynomial(poly) + r.clone() * y
            },
            &|index| {
                let y = Expression::Challenge(index + num_challenges);
                // fold variable x_i -> x_i + r * y_i
                Expression::Challenge(index) + r.clone() * y
            },
            &|a| -a,
            &|a, b| a + b,
            &|a, b| a * b,
            &|a, k| a * k,
        )
    }

    fn visualize(&self) -> String {
        self.evaluate(
            &|c| trim_leading_zeros(format!("{:?}", c)),
            &|poly| {
                let rotation = match poly.rotation.0.cmp(&0) {
                    Ordering::Equal => "".to_owned(),
                    Ordering::Less => format!("[{}]", poly.rotation.0),
                    Ordering::Greater => format!("[+{}]", poly.rotation.0),
                };
                format!("Z_{}{}", poly.index, rotation)
            },
            &|index| format!("r_{}", index),
            &|a| format!("(-{})", a),
            &|a, b| format!("({} + {})", a, b),
            &|a, b| format!("({} * {})", a, b),
            &|a, k| format!("{:?} * {}", trim_leading_zeros(format!("{:?}", k)), a),
        )
    }

    pub fn from_halo2_expr(expr: &PE<F>, num_selector: usize, num_fixed: usize) -> Self {
        match expr {
            PE::Constant(c) => Expression::Constant(*c),
            PE::Selector(sel) => Expression::Polynomial(Query {
                index: sel.index(),
                rotation: Rotation(0),
            }),
            PE::Fixed(query) => Expression::Polynomial(Query {
                index: num_selector + query.column_index(),
                rotation: query.rotation(),
            }),
            PE::Advice(query) => Expression::Polynomial(Query {
                index: num_selector + num_fixed + query.column_index(),
                rotation: query.rotation(),
            }),
            PE::Negated(a) => {
                let a = Self::from_halo2_expr(a, num_selector, num_fixed);
                -a
            }
            PE::Sum(a, b) => {
                let a = Self::from_halo2_expr(a, num_selector, num_fixed);
                let b = Self::from_halo2_expr(b, num_selector, num_fixed);
                a + b
            }
            PE::Product(a, b) => {
                let a = Self::from_halo2_expr(a, num_selector, num_fixed);
                let b = Self::from_halo2_expr(b, num_selector, num_fixed);
                a * b
            }
            PE::Scaled(a, k) => {
                let a = Self::from_halo2_expr(a, num_selector, num_fixed);
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

        let monomials = self
            .monomials
            .par_iter()
            .map(|f| f.homogeneous(degree, offset, u_index))
            .collect();

        Self {
            arity: self.arity + 1,
            monomials,
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

        debug!("monomials len {}", self.monomials.len());

        poly.monomials.extend(
            self.monomials
                .par_iter()
                .filter_map(|mono| {
                    mono.exponents.get(*index)?.eq(&degree).then(|| {
                        let mut exponents = mono.exponents.clone();
                        exponents.remove(*index);
                        Monomial::new(index_to_poly.clone(), mono.coeff, exponents)
                    })
                })
                .collect::<Vec<_>>(),
        );

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
            format!("{}", expr3.expand().homogeneous(0)),
            "(r_0^2) + (Z_0)(r_0) + (Z_0)(Z_1)"
        );
    }
}
