use std::{
    collections::HashMap,
    ops::{Add, Mul, Sub},
};

use ff::PrimeField;
use itertools::*;

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

impl<F: PrimeField> From<HashMap<usize, Expression<F>>> for GroupedPoly<F> {
    fn from(value: HashMap<usize, Expression<F>>) -> Self {
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
    fn iter(&self) -> impl Iterator<Item = (usize, &Expression<F>)> {
        self.terms
            .iter()
            .enumerate()
            .filter_map(|(degree, expr)| expr.as_ref().map(|expr| (degree, expr)))
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

#[cfg(test)]
mod test {
    use crate::polynomial::Query;

    use ff::Field;
    use halo2_proofs::poly::Rotation;
    use halo2curves::pasta::Fq;
    use maplit::hashmap as map;

    use super::*;

    #[test]
    fn simple_add() {
        let mut actual = GroupedPoly::<Fq>::from(map! {
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
        .iter()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();
        actual.sort();

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
        let mut actual = GroupedPoly::<Fq>::from(map! {
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
        .iter()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();
        actual.sort();

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
        let mut actual = GroupedPoly::<Fq>::from(map! {
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
        .iter()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();
        actual.sort();

        assert_eq!(actual, vec!["18;(Z_0)(Z_2)(Z_3) + (Z_2)(Z_3)(Z_1[+1])"]);
    }

    #[test]
    fn mul() {
        let mut actual = GroupedPoly::<Fq>::from(map! {
                2 => Expression::Polynomial(Query { index: 0, rotation: Rotation(0) }),
                3 => Expression::Polynomial(Query { index: 1, rotation: Rotation(0) }),
                4 => Expression::Polynomial(Query { index: 2, rotation: Rotation(0) }),
        })
        .mul(GroupedPoly::<Fq>::from(map! {
            2 => Expression::Polynomial(Query { index: 3, rotation: Rotation(0) }),
            3 => Expression::Polynomial(Query { index: 4, rotation: Rotation(0) }),
            4 => Expression::Polynomial(Query { index: 5, rotation: Rotation(0) }),
        }))
        .iter()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();
        actual.sort();

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
}
