use std::{
    collections::{hash_map::Entry, HashMap},
    convert,
    ops::{Add, Mul, Neg, Sub},
};

use ff::PrimeField;

use super::{Expression, Query};

pub type Degree = usize;

/// Polynome grouped by degrees
///
/// We mean some challenge and its degrees are represented as [`GroupedPoly::term`] keys, and
/// coefficients are represented as [`GroupedPoly::term`] values
///
/// `x^0 * a + x^1 * b + x^3 * c -> { 0 => a, 1 => b, 3 => c }`
pub struct GroupedPoly<F> {
    // TODO #159 depend on `evaluate` algo, can be changed to `BTreeMap`
    terms: HashMap<Degree, Expression<F>>,
}

impl<F: PrimeField> GroupedPoly<F> {
    fn aggregate(mut self, degree: usize, expr: Expression<F>) -> Self {
        match self.terms.entry(degree) {
            Entry::Vacant(vacant) => {
                vacant.insert(expr);
            }
            Entry::Occupied(mut occupied) => {
                occupied.insert(Expression::Sum(
                    Box::new(occupied.get().clone()),
                    Box::new(expr),
                ));
            }
        }
        self
    }

    // fold transform
    // here self is Expression<F>
    pub fn fold_transform(&self, _mm: usize, _nn: usize) -> Self {
        let num_challenges = self.num_challenges();
        let _r = Expression::<F>::Challenge(2 * num_challenges);

        todo!("Part of #159")
    }

    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        _constant: &impl Fn(F) -> T,
        _poly: &impl Fn(Query) -> T,
        _challenge: &impl Fn(usize) -> T,
        _negated: &impl Fn(T) -> T,
        _sum: &impl Fn(T, T) -> T,
        _product: &impl Fn(T, T) -> T,
        _scaled: &impl Fn(T, F) -> T,
    ) -> T {
        todo!("Part of #159")
    }

    pub fn num_challenges(&self) -> usize {
        self.terms.values().map(|expr| expr.num_challenges()).sum()
    }
}

impl<F> Default for GroupedPoly<F> {
    fn default() -> Self {
        Self {
            terms: Default::default(),
        }
    }
}

macro_rules! impl_poly_ops {
    ($trait:ident, $method:ident, $variant:ident, $rhs_expr: expr) => {
        impl<F: PrimeField> $trait for GroupedPoly<F> {
            type Output = Self;

            fn $method(mut self, rhs: Self) -> Self::Output {
                rhs.terms.into_iter().for_each(|(degree, rhs_expr)| {
                    match self.terms.entry(degree) {
                        Entry::Vacant(vacant) => {
                            vacant.insert(rhs_expr);
                        }
                        Entry::Occupied(mut occupied) => {
                            occupied.insert(Expression::$variant(
                                Box::new(occupied.get().clone()),
                                Box::new($rhs_expr(rhs_expr)),
                            ));
                        }
                    }
                });

                self
            }
        }
    };
}

impl_poly_ops!(Add, add, Sum, convert::identity);
impl_poly_ops!(Sub, sub, Sum, Neg::neg);

impl<F: PrimeField> Neg for GroupedPoly<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            terms: self
                .terms
                .into_iter()
                .map(|(k, v)| (k, Neg::neg(v)))
                .collect(),
        }
    }
}

impl<F: PrimeField> Mul for GroupedPoly<F> {
    type Output = GroupedPoly<F>;
    fn mul(self, rhs: GroupedPoly<F>) -> Self::Output {
        let mut res = GroupedPoly::default();
        for (lhs_degree, lhs_expr) in self.terms.into_iter() {
            for (rhs_degree, rhs_expr) in rhs.terms.iter() {
                let degree = lhs_degree + rhs_degree;
                let expr = lhs_expr.clone() * rhs_expr.clone();

                match res.terms.entry(degree) {
                    Entry::Occupied(mut occupied) => {
                        let current = Box::new(occupied.get().clone());
                        occupied.insert(Expression::Sum(current, Box::new(expr)));
                    }
                    Entry::Vacant(vacant) => {
                        vacant.insert(expr);
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
        let mut actual = GroupedPoly::<Fq> {
            terms: map! {
                0 => Expression::Constant(Fq::from_u128(u128::MAX)),
                1 => Expression::Polynomial(Query {
                    index: 0,
                    rotation: Rotation(0)
                }),
                5 => Expression::Challenge(0),
            },
        }
        .add(GroupedPoly::<Fq> {
            terms: map! {
                0 => Expression::Challenge(0),
                2 => Expression::Polynomial(Query {
                    index: 5,
                    rotation: Rotation(-2)
                }),
                5 => Expression::Constant(Fq::ONE),
            },
        })
        .terms
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
        let mut actual = GroupedPoly::<Fq> {
            terms: map! {
                0 => Expression::Constant(Fq::from_u128(u128::MAX)),
                1 => Expression::Polynomial(Query {
                    index: 0,
                    rotation: Rotation(0)
                }),
                5 => Expression::Constant(Fq::ONE),
            },
        }
        .sub(GroupedPoly::<Fq> {
            terms: map! {
                0 => Expression::Challenge(0),
                2 => Expression::Polynomial(Query {
                    index: 5,
                    rotation: Rotation(-2)
                }),
                5 => Expression::Challenge(0),
            },
        })
        .terms
        .iter()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();
        actual.sort();

        assert_eq!(
            actual,
            vec![
                "0;0xffffffffffffffffffffffffffffffff + 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000(r_0)",
                "1;(Z_0)",
                "2;(Z_5[-2])",
                "5;0x1 + 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000(r_0)"
            ]
        );
    }

    #[test]
    fn simple_mul() {
        let mut actual = GroupedPoly::<Fq> {
            terms: map! {
                9 => Expression::Sum(
                    Box::new(Expression::Polynomial(Query { index: 0, rotation: Rotation(0) })),
                    Box::new(Expression::Polynomial(Query { index: 1, rotation: Rotation(1) }))
                ),
            },
        }
        .mul(GroupedPoly::<Fq> {
            terms: map! {
                9 => Expression::Product(
                    Box::new(Expression::Polynomial(Query { index: 2, rotation: Rotation(0) })),
                    Box::new(Expression::Polynomial(Query { index: 3, rotation: Rotation(0) }))
                ),
            },
        })
        .terms
        .iter()
        .map(|(degree, term)| format!("{degree};{}", term.expand()))
        .collect::<Vec<_>>();
        actual.sort();

        assert_eq!(actual, vec!["18;(Z_0)(Z_2)(Z_3) + (Z_2)(Z_3)(Z_1[+1])"]);
    }

    #[test]
    fn mul() {
        let mut actual = GroupedPoly::<Fq> {
            terms: map! {
                2 => Expression::Polynomial(Query { index: 0, rotation: Rotation(0) }),
                3 => Expression::Polynomial(Query { index: 1, rotation: Rotation(0) }),
                4 => Expression::Polynomial(Query { index: 2, rotation: Rotation(0) }),
            },
        }
        .mul(GroupedPoly::<Fq> {
            terms: map! {
                2 => Expression::Polynomial(Query { index: 3, rotation: Rotation(0) }),
                3 => Expression::Polynomial(Query { index: 4, rotation: Rotation(0) }),
                4 => Expression::Polynomial(Query { index: 5, rotation: Rotation(0) }),
            },
        })
        .terms
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
