use std::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    collections::{HashMap, HashSet},
    fmt,
    fmt::{Debug, Display},
    ops::{Add, Mul, Neg, Sub},
};

use ff::PrimeField;
use halo2_proofs::{arithmetic::CurveAffine, plonk::Expression as PE, poly::Rotation};

use crate::{plonk::lookup::LookupEvalDomain, plonk::PlonkEvalDomain, util::trim_leading_zeros};

pub mod sparse;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Query {
    pub index: usize,
    pub rotation: Rotation,
}

#[derive(Clone, Debug, PartialEq)]
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
    pub fn poly_set(&self, set: &mut HashSet<(i32, usize, usize)>) {
        match self {
            Expression::Constant(_) => (),
            Expression::Polynomial(poly) => {
                set.insert((poly.rotation.0, poly.index, 0));
            }
            Expression::Challenge(index) => {
                set.insert((0, *index, 1));
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
        let mut set = HashSet::<(i32, usize, usize)>::new();
        self._num_challenges(&mut set);
        set.len()
    }

    pub fn _num_challenges(&self, set: &mut HashSet<(i32, usize, usize)>) {
        match self {
            Expression::Constant(_) => (),
            Expression::Polynomial(_) => (),
            Expression::Challenge(index) => {
                set.insert((0, *index, 1));
            }
            Expression::Negated(a) => a._num_challenges(set),
            Expression::Sum(a, b) => {
                a._num_challenges(set);
                b._num_challenges(set);
            }
            Expression::Product(a, b) => {
                a._num_challenges(set);
                b._num_challenges(set);
            }
            Expression::Scaled(a, _) => a._num_challenges(set),
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

    fn _expand(&self, index_to_poly: &Vec<(i32, usize, usize)>) -> MultiPolynomial<F> {
        self.evaluate(
            &|c| {
                let arity = index_to_poly.len();
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.clone(), c, vec![0; arity])],
                }
            },
            &|poly| {
                let arity = index_to_poly.len();
                let mut exponents = vec![0; arity];
                let index = index_to_poly
                    .iter()
                    .position(|&(a, b, t)| a == poly.rotation.0 && b == poly.index && t == 0)
                    .unwrap();
                exponents[index] = 1;
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.clone(), F::ONE, exponents)],
                }
            },
            &|cha_index| {
                let arity = index_to_poly.len();
                let mut exponents = vec![0; arity];
                let index = index_to_poly
                    .iter()
                    .position(|&(a, b, t)| a == 0 && b == cha_index && t == 1)
                    .unwrap();
                exponents[index] = 1;
                MultiPolynomial {
                    arity,
                    monomials: vec![Monomial::new(index_to_poly.clone(), F::ONE, exponents)],
                }
            },
            &|a| -a,
            &|a, b| a + b,
            &|a, b| a * b,
            &|a, k| a * k,
        )
    }

    pub fn expand(&self) -> MultiPolynomial<F> {
        let mut set = HashSet::new();
        self.poly_set(&mut set);
        let mut index_to_poly: Vec<(i32, usize, usize)> = set.into_iter().collect();
        index_to_poly.sort();
        self._expand(&index_to_poly)
    }

    // fold_transform will fold a polynomial expression P(f_1,...f_m, x_1,...,x_n)
    // and output P(f_1,...,f_m, x_1+r*y_1,...,x_n+r*y_n)
    // here mm = num_fixed+num_selectors
    // nn = num_advice
    pub fn fold_transform(&self, mm: usize, nn: usize) -> Self {
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
// type=0 => poly with (rotation, column_index, 0)
// type=1 => challenge with (0, index, 1)
#[derive(Clone)]
pub struct Monomial<F: PrimeField> {
    pub arity: usize,
    // poly or challenge: (rotation, column_index, type)
    pub index_to_poly: Vec<(i32, usize, usize)>,
    // (rotation, column_index, var_type) -> index
    // when type = 1 as a challenge, we always set rotation = 0
    pub poly_to_index: HashMap<(i32, usize, usize), usize>,
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
            let (rid, cid, var_type) = self.index_to_poly[i];
            let shift = match rid.cmp(&0) {
                Ordering::Equal => "".to_owned(),
                Ordering::Greater => format!("[+{rid}]"),
                Ordering::Less => format!("[{rid}]"),
            };

            match var_type {
                0 => {
                    if *exp == 1 {
                        write!(f, "(Z_{}{})", cid, shift)?;
                    } else {
                        write!(f, "(Z_{}{}^{})", cid, shift, exp)?;
                    }
                }
                1 => {
                    if *exp == 1 {
                        write!(f, "(r_{})", cid)?;
                    } else {
                        write!(f, "(r_{}^{})", cid, exp)?;
                    }
                }
                _ => unimplemented!("other variable type not supported"),
            }
        }
        write!(f, "")
    }
}

impl<F: PrimeField> Monomial<F> {
    pub fn new(index_to_poly: Vec<(i32, usize, usize)>, coeff: F, exponents: Vec<usize>) -> Self {
        let arity = index_to_poly.len();
        assert!(arity == exponents.len());
        let mut poly_to_index: HashMap<(i32, usize, usize), usize> = HashMap::new();
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

    /// offset = num_selector+num_fixed, equals number of variables that are not folded,
    pub fn homogeneous(&self, degree: usize, offset: usize, u_index: usize) -> Self {
        let mut mono = self.clone();
        mono.arity += 1;
        mono.exponents
            .push(degree - self.degree_for_folding(offset));
        mono.index_to_poly.push((0, u_index, 1));
        mono.poly_to_index.insert((0, u_index, 1), mono.arity);
        mono
    }

    pub fn to_expression(&self) -> Expression<F> {
        let mut expr = Expression::Constant(self.coeff);
        for (i, exp) in self.exponents.iter().enumerate() {
            let (rot, idx, var_type) = self.index_to_poly[i];
            match var_type {
                0 => {
                    for _ in 0..(*exp) {
                        let x0 = Expression::<F>::Polynomial(Query {
                            index: idx,
                            rotation: Rotation(rot),
                        });
                        expr = Expression::Product(Box::new(expr), Box::new(x0));
                    }
                }
                1 => {
                    for _ in 0..(*exp) {
                        let r = Expression::<F>::Challenge(idx);
                        expr = Expression::Product(Box::new(expr), Box::new(r));
                    }
                }
                _ => unimplemented!("variable type not supported"),
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
            .filter_map(|(exp, (_, col_index, _))| (col_index >= &offset).then_some(exp))
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

pub trait Eval<T, F> {
    fn eval(&self, row: usize, data: &T) -> F;
}

impl<'a, C, F> Eval<PlonkEvalDomain<'a, C, F>, F> for Monomial<F>
where
    F: PrimeField,
    C: CurveAffine<ScalarExt = F>,
{
    /// evaluate monomial over {x_1,...,x_n}, n = self.arity
    /// first get the value of x_i according to its (row, col) in the plonk table
    /// then calculate the evaluation of monomial: c*x_1^{d_1}*...*x_n^{d_n}
    fn eval(&self, row: usize, data: &PlonkEvalDomain<C, F>) -> F {
        let PlonkEvalDomain { S, U1, W1, U2, W2 } = data;
        let num_selectors = S.selectors.len();
        let offset = S.fixed_columns.len() + num_selectors;
        let num_advice = S.num_advice_columns;
        let y1_index = offset + num_advice;
        let u1_index = y1_index + 1;
        let y2_index = offset + 2 * num_advice + 2;
        let u2_index = y2_index + 1;

        let row_size = W1.W.len() / num_advice;
        let vars: Vec<F> = (0..self.arity)
            .map(|i| {
                let (rot, col, _var_type) = self.index_to_poly[i];
                // TODO: add eval for challenge
                let row1 = if (rot + row as i32) >= 0 {
                    rot as usize + row
                } else {
                    // TODO: check how halo2 handle
                    // (1): row+rot<0
                    // (2): row+rot>=2^K
                    row_size - (-rot as usize) + row
                };
                // layout of the index is:
                // |num_selectors|num_fixed|num_advice|y1|u1|num_advice2|y2|u2|
                // given column index of a variable x_i, we are able to find the correct location of that variable
                // and hence its value
                match col {
                    // selector column
                    col if col < num_selectors => {
                        if S.selectors[col][row1] {
                            F::ONE
                        } else {
                            F::ZERO
                        }
                    }
                    // fixed column
                    col if col < offset => S.fixed_columns[col - num_selectors][row1],
                    // advice column for (U1, W1)
                    col if col < y1_index => W1.W[(col - offset) * row_size + row1],
                    // challenge y1
                    col if col == y1_index => U1.y,
                    // homogeneous variable u1
                    col if col == u1_index => U1.u,
                    // advice column for (U2, W2)
                    col if col < y2_index => W2.W[(col - u1_index - 1) * row_size + row1],
                    // challenge y2
                    col if col == y2_index => U2.y,
                    // homogenous variable u2
                    col if col == u2_index => U2.u,
                    col => panic!("index out of boundary: {col}"),
                }
            })
            .collect();

        vars.into_iter()
            .zip(self.exponents.iter())
            .map(|(x, exp)| x.pow([*exp as u64, 0, 0, 0]))
            .fold(self.coeff, |acc, v| acc * v)
    }
}

impl<'a, F: PrimeField> Eval<LookupEvalDomain<'a, F>, F> for Monomial<F> {
    /// evaluate monomial over {x_1,...,x_n}, n = self.arity
    /// first get the value of x_i according to its (row, col) in the plonk table
    /// then calculate the evaluation of monomial: c*x_1^{d_1}*...*x_n^{d_n}
    fn eval(&self, _row: usize, _data: &LookupEvalDomain<F>) -> F {
        todo!()
    }
}

#[derive(Clone, PartialEq)]
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
    // mm = num_fixed + num_selectors, nn = num_advice
    pub fn fold_transform(&self, mm: usize, nn: usize) -> Self {
        self.homogeneous(mm)
            .to_expression()
            .fold_transform(mm, nn)
            .expand()
    }

    // get coefficient of X^k, where X identified by (ratation, index, var_type) in 0..arity, k=degree
    pub fn coeff_of(&self, var: (i32, usize, usize), degree: usize) -> Self {
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
            } else if self.monomials[idx].coeff == F::ZERO {
                continue;
            } else {
                reduced.push(self.monomials[idx].clone());
            }
        }
        self.monomials = reduced;
    }

    // evaluate the multipoly
    pub fn eval<T>(&self, row: usize, data: &T) -> F
    where
        Monomial<F>: Eval<T, F>,
    {
        self.monomials
            .iter()
            .map(|mono| mono.eval(row, data))
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
            format!("{}", expr3.expand().homogeneous(0)),
            "(r_0^2) + (Z_0)(r_0) + (Z_0)(Z_1)"
        );
    }
}
