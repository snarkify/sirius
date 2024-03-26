use std::{
    collections::{hash_map::Entry, HashMap},
    ops::{Add, Mul, Sub},
};

use ff::PrimeField;

use super::Expression;

pub type Degree = usize;

pub struct FoldingPoly<F> {
    // TODO #159 depend on `evaluate` algo, can be changed to `BTreeMap`
    terms: HashMap<Degree, Expression<F>>,
}
impl<F> Default for FoldingPoly<F> {
    fn default() -> Self {
        Self {
            terms: Default::default(),
        }
    }
}

macro_rules! impl_poly_ops {
    ($trait:ident, $method:ident, $variant:ident, $rhs_expr: expr) => {
        impl<F: PrimeField> $trait for FoldingPoly<F> {
            type Output = FoldingPoly<F>;

            fn $method(mut self, rhs: FoldingPoly<F>) -> Self::Output {
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

impl_poly_ops!(Add, add, Sum, std::convert::identity);
impl_poly_ops!(Sub, sub, Sum, std::ops::Neg::neg);
impl_poly_ops!(Mul, mul, Product, std::convert::identity);

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
        let mut actual = FoldingPoly::<Fq> {
            terms: map! {
                0 => Expression::Constant(Fq::from_u128(u128::MAX)),
                1 => Expression::Polynomial(Query {
                    index: 0,
                    rotation: Rotation(0)
                }),
                5 => Expression::Challenge(0),
            },
        }
        .add(FoldingPoly::<Fq> {
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
        let mut actual = FoldingPoly::<Fq> {
            terms: map! {
                0 => Expression::Constant(Fq::from_u128(u128::MAX)),
                1 => Expression::Polynomial(Query {
                    index: 0,
                    rotation: Rotation(0)
                }),
                5 => Expression::Constant(Fq::ONE),
            },
        }
        .sub(FoldingPoly::<Fq> {
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
        let mut actual = FoldingPoly::<Fq> {
            terms: map! {
                0 => Expression::Constant(Fq::from_u128(u128::MAX)),
                1 => Expression::Polynomial(Query {
                    index: 0,
                    rotation: Rotation(0)
                }),
                5 => Expression::Constant(Fq::ONE),
                9 => Expression::Challenge(9),
            },
        }
        .mul(FoldingPoly::<Fq> {
            terms: map! {
                0 => Expression::Challenge(0),
                2 => Expression::Polynomial(Query {
                    index: 5,
                    rotation: Rotation(-2)
                }),
                5 => Expression::Challenge(0),
                9 => Expression::Challenge(9),
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
                "0;0xffffffffffffffffffffffffffffffff(r_0)",
                "1;(Z_0)",
                "2;(Z_5[-2])",
                "5;(r_0)",
                "9;(r_9^2)"
            ]
        );
    }
}
