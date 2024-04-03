use std::ops::{Add, Mul, Neg, Sub};

use ff::PrimeField;
use itertools::*;

use crate::polynomial::Query;

use super::Expression;

/// Polynome grouped by degrees
///
/// We mean some challenge and its degrees are represented as [`GroupedPoly::term`] keys, and
/// coefficients are represented as [`GroupedPoly::term`] values
///
/// `x^0 * a + x^1 * b + x^3 * c -> { 0 => a, 1 => b, 3 => c }`
pub struct GroupedPoly<F> {
    // TODO #159 depend on `evaluate` algo, can be changed to `BTreeMap`
    terms: Vec<Option<Expression<F>>>,
}
impl<F> Default for GroupedPoly<F> {
    fn default() -> Self {
        Self {
            terms: Default::default(),
        }
    }
}

impl<IT: IntoIterator<Item = (usize, Expression<F>)>, F: PrimeField> From<IT> for GroupedPoly<F> {
    fn from(value: IT) -> Self {
        let mut self_ = Self::default();

        for (degree, expr) in value.into_iter() {
            if degree >= self_.terms.len() {
                self_.terms.resize(degree + 1, None);
            }

            self_.terms[degree] = Some(expr);
        }

        self_
    }
}

impl<F: PrimeField> GroupedPoly<F> {
    /// This function converts an arbitrary expression into a [`GroupedPoly`], by selecting new
    /// [`Expression::Polynomial`] & [`Expression::Challenge`]
    ///
    /// Since they are labelled using a sequential index, to select new ones we need to know the
    /// ones that are not already occupied. Moreover, we need a one-to-one correspondence for each
    /// polynomial and challenge.
    ///
    /// Therefore, `num_of_poly` & `num_of_challenge` are used as input parameters, which allow us to
    /// allocate a polynomial `x + num_of_poly` for polynomial `x` and for challenge respectively.
    ///
    /// ## Example
    ///
    /// ```math
    /// P(a, b, c, d, e) &= (a + b + c) * (d + e) =>
    ///     [a1 + b1 + c1 + k * (a2 + b2 + c2)] & [d1 + e1 + k * (d2 + e2)]
    ///     =
    ///     (a1 + b1 + c1)(d1 + e1)                             * k^0 +
    ///     [(a2 + b2 + c2)(d1 + e1) + (a1 + b1 + c1)(d2 + e2)] * k^1 +
    ///     (a2 + b2 + c2)(d2 + e2)                             * k^2
    ///     =
    ///     a1*d1 + a1*e1 + b1*d1 + b1*e1 + c1*d1 + c1*e1       * k^0 +
    ///     a2*d1 + a2*e1 + b2*d1 + b2*e1 + c2*d1 + c2*e1 + a1*d2 + a1*e2 + b1*d2 + b1*e2 + c1*d2 + c1*e2 * k^1 +
    ///     a2*d2 + a2*e2 + b2*d2 + b2*e2 + c2*d2 + c2*e2       * k^2
    /// ```
    pub fn new(expr: &Expression<F>, num_of_poly: usize, num_of_challenge: usize) -> Self {
        expr.evaluate(
            &|constant| GroupedPoly {
                terms: vec![Some(Expression::Constant(constant))],
            },
            &|poly| {
                let y = Expression::Polynomial(Query {
                    index: poly.index + num_of_poly,
                    rotation: poly.rotation,
                });

                GroupedPoly {
                    terms: vec![Some(Expression::Polynomial(poly)), Some(y)],
                }
            },
            &|challenge_index| {
                let y = Expression::Challenge(challenge_index + num_of_challenge);

                GroupedPoly {
                    terms: vec![Some(Expression::Challenge(challenge_index)), Some(y)],
                }
            },
            &|a| -a,
            &|a, b| a + b,
            &|a, b| a * b,
            &|a, k| a * k,
        )
    }

    fn iter_with_degree(&self) -> impl Iterator<Item = (usize, &Expression<F>)> {
        self.terms
            .iter()
            .enumerate()
            .filter_map(|(degree, expr)| expr.as_ref().map(|expr| (degree, expr)))
    }

    pub fn iter(&self) -> impl Iterator<Item = &Option<Expression<F>>> {
        self.terms.iter()
    }
}

macro_rules! impl_poly_ops {
    ($trait:ident, $method:ident, $variant:ident, $rhs_expr: expr) => {
        impl<F: PrimeField> $trait for GroupedPoly<F> {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self::Output {
                use EitherOrBoth::*;

                Self {
                    terms: self
                        .terms
                        .into_iter()
                        .zip_longest(rhs.terms.into_iter())
                        .map(|entry| match entry {
                            Both(Some(lhs), Some(rhs)) => Some(Expression::$variant(
                                Box::new(lhs),
                                Box::new($rhs_expr(rhs)),
                            )),
                            Both(None, Some(rhs)) | Right(Some(rhs)) => Some($rhs_expr(rhs)),
                            Both(Some(lhs), None) | Left(Some(lhs)) => Some(lhs),
                            Both(None, None) | Left(None) | Right(None) => None,
                        })
                        .collect(),
                }
            }
        }
    };
}

impl_poly_ops!(Add, add, Sum, std::convert::identity);
impl_poly_ops!(Sub, sub, Sum, std::ops::Neg::neg);

impl<F: PrimeField> Mul<F> for GroupedPoly<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self::Output {
        Self {
            terms: self
                .terms
                .into_iter()
                .map(|expr| {
                    expr.map(|expr| {
                        Expression::Product(Box::new(Expression::Constant(rhs)), Box::new(expr))
                    })
                })
                .collect(),
        }
    }
}

impl<F: PrimeField> Mul for GroupedPoly<F> {
    type Output = GroupedPoly<F>;
    fn mul(self, rhs: GroupedPoly<F>) -> Self::Output {
        let mut res = GroupedPoly::default();
        res.terms.resize(self.terms.len() * rhs.terms.len(), None);

        for (lhs_degree, lhs_expr) in self
            .terms
            .into_iter()
            .enumerate()
            .filter_map(|(degree, expr)| Some((degree, expr?)))
        {
            for (rhs_degree, rhs_expr) in rhs
                .terms
                .clone()
                .into_iter()
                .enumerate()
                .filter_map(|(degree, expr)| Some((degree, expr?)))
            {
                let degree = lhs_degree + rhs_degree;
                let expr = lhs_expr.clone() * rhs_expr.clone();

                let entry = res
                    .terms
                    .get_mut(degree)
                    .expect("safe because resize at the top");

                match entry.take() {
                    Some(current) => {
                        *entry = Some(Expression::Sum(Box::new(current), Box::new(expr)));
                    }
                    None => {
                        *entry = Some(expr);
                    }
                }
            }
        }
        res
    }
}

impl<F: PrimeField> Neg for GroupedPoly<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            terms: self
                .terms
                .into_iter()
                .map(|expr| expr.map(Neg::neg))
                .collect(),
        }
    }
}

#[cfg(test)]
mod test {
    use std::array;

    use ff::Field;
    use halo2_proofs::poly::Rotation;
    use halo2curves::pasta::Fq;
    use maplit::hashmap as map;

    use super::*;

    #[test]
    fn simple_add() {
        let actual = GroupedPoly::<Fq>::from(map! {
            0 => Expression::Constant(Fq::from_u128(u128::MAX)),
            1 => Expression::Polynomial(Query {
                index: 0,
                rotation: Rotation(0)
            }),
            5 => Expression::Challenge(0),
        })
        .add(GroupedPoly::<Fq>::from(map! {
            0 => Expression::Challenge(0),
            2 => Expression::Polynomial(Query {
                index: 5,
                rotation: Rotation(-2)
            }),
            5 => Expression::Constant(Fq::ONE),
        }))
        .iter_with_degree()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();

        assert_eq!(
            actual,
            vec![
                "0;0xffffffffffffffffffffffffffffffff + (r_0)",
                "1;(Z_0)",
                "2;(Z_5[-2])",
                "5;0x1 + (r_0)"
            ]
        );
    }

    #[test]
    fn simple_sub() {
        let actual = GroupedPoly::<Fq>::from(map! {
            0 => Expression::Constant(Fq::from_u128(u128::MAX)),
            1 => Expression::Polynomial(Query {
                index: 0,
                rotation: Rotation(0)
            }),
            5 => Expression::Constant(Fq::ONE),
        })
        .sub(GroupedPoly::<Fq>::from(map! {
            0 => Expression::Challenge(0),
            2 => Expression::Polynomial(Query {
                index: 5,
                rotation: Rotation(-2)
            }),
            5 => Expression::Challenge(0),
        }))
        .iter_with_degree()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();

        assert_eq!(
            actual,
            vec![
                "0;0xffffffffffffffffffffffffffffffff + 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000(r_0)",
                "1;(Z_0)",
                "2;0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000(Z_5[-2])",
                "5;0x1 + 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000(r_0)"
            ]
        );
    }

    #[test]
    fn simple_mul() {
        let actual = GroupedPoly::<Fq>::from(map! {
            9 => Expression::Sum(
                Box::new(Expression::Polynomial(Query { index: 0, rotation: Rotation(0) })),
                Box::new(Expression::Polynomial(Query { index: 1, rotation: Rotation(1) }))
            ),
        })
        .mul(GroupedPoly::<Fq>::from(map! {
            9 => Expression::Product(
                Box::new(Expression::Polynomial(Query { index: 2, rotation: Rotation(0) })),
                Box::new(Expression::Polynomial(Query { index: 3, rotation: Rotation(0) }))
            ),
        }))
        .iter_with_degree()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();

        assert_eq!(actual, vec!["18;(Z_0)(Z_2)(Z_3) + (Z_2)(Z_3)(Z_1[+1])"]);
    }

    #[test]
    fn mul() {
        let actual = GroupedPoly::<Fq>::from(map! {
                2 => Expression::Polynomial(Query { index: 0, rotation: Rotation(0) }),
                3 => Expression::Polynomial(Query { index: 1, rotation: Rotation(0) }),
                4 => Expression::Polynomial(Query { index: 2, rotation: Rotation(0) }),
        })
        .mul(GroupedPoly::<Fq>::from(map! {
            2 => Expression::Polynomial(Query { index: 3, rotation: Rotation(0) }),
            3 => Expression::Polynomial(Query { index: 4, rotation: Rotation(0) }),
            4 => Expression::Polynomial(Query { index: 5, rotation: Rotation(0) }),
        }))
        .iter_with_degree()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();

        assert_eq!(
            actual,
            vec![
                "4;(Z_0)(Z_3)",
                "5;(Z_1)(Z_3) + (Z_0)(Z_4)",
                "6;(Z_2)(Z_3) + (Z_1)(Z_4) + (Z_0)(Z_5)",
                "7;(Z_2)(Z_4) + (Z_1)(Z_5)",
                "8;(Z_2)(Z_5)"
            ]
        );
    }

    #[test]
    fn creation() {
        // P(a, b, c, d, e) &= (a + b + c) * (d + e) =>
        //     [a1 + b1 + c1 + k* (a2 + b2 + c2)] & [d1 + e1 + k * (d2 + e2)]
        //
        //     =
        //
        //     (a1 + b1 + c1)(d1 + e1)                             * k^0 +
        //     [(a2 + b2 + c2)(d1 + e1) + (a1 + b1 + c1)(d2 + e2)] * k^1 +
        //     (a2 + b2 + c2)(d2 + e2)                             * k^2
        //
        //     =
        //
        //     a1*d1 + a1*e1 + b1*d1 + b1*e1 + c1*d1 + c1*e1       * k^0 +
        //     a2*d1 + a2*e1 + b2*d1 + b2*e1 + c2*d1 + c2*e1 + a1*d2 + a1*e2 + b1*d2 + b1*e2 + c1*d2 + c1*e2 * k^1 +
        //     a2*d2 + a2*e2 + b2*d2 + b2*e2 + c2*d2 + c2*e2       * k^2

        fn sum(expr: &[Expression<Fq>]) -> Box<Expression<Fq>> {
            Box::new(match expr.split_first() {
                Some((first, rest)) => Expression::Sum(Box::new(first.clone()), sum(rest)),
                None => Expression::Constant(Fq::ZERO),
            })
        }

        let [a, b, c, d, e] = array::from_fn(|index| {
            Expression::Polynomial(Query {
                index,
                rotation: Rotation(0),
            })
        });

        let grouped_poly =
            GroupedPoly::new(Expression::Product(sum(&[a, b, c]), sum(&[d, e])), 5, 0);

        let actual = grouped_poly
            .iter_with_degree()
            .map(|(degree, term)| format!("{degree};{}", term.expand()))
            .collect::<Vec<_>>();

        assert_eq!(
            actual,
            vec![
                "0;(Z_0)(Z_3) + (Z_1)(Z_3) + (Z_2)(Z_3) + (Z_0)(Z_4) + (Z_1)(Z_4) + (Z_2)(Z_4)",
                "1;(Z_3)(Z_5) + (Z_4)(Z_5) + (Z_3)(Z_6) + (Z_4)(Z_6) + (Z_3)(Z_7) + (Z_4)(Z_7) + (Z_0)(Z_8) + (Z_1)(Z_8) + (Z_2)(Z_8) + (Z_0)(Z_9) + (Z_1)(Z_9) + (Z_2)(Z_9)",
                "2;(Z_5)(Z_8) + (Z_6)(Z_8) + (Z_7)(Z_8) + (Z_5)(Z_9) + (Z_6)(Z_9) + (Z_7)(Z_9)"
            ]
        );
    }
}
