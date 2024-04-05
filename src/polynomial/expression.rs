use std::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    collections::{BTreeSet, HashSet},
    fmt,
    fmt::{Debug, Display},
    ops::{self, Add, Mul, Neg, Sub},
};

use ff::PrimeField;
use halo2_proofs::{plonk::Expression as PE, poly::Rotation};
use serde::Serialize;

use super::{Monomial, MultiPolynomial};

use crate::util::trim_leading_zeros;
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

impl Query {
    pub fn is_advice(&self, num_selectors: usize, num_fixed: usize) -> bool {
        self.index >= num_selectors + num_fixed
    }
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

impl<F: Default> Default for Expression<F> {
    fn default() -> Self {
        Expression::Constant(F::default())
    }
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

    pub fn expand(&self) -> MultiPolynomial<F> {
        let mut set = BTreeSet::new();
        self.poly_set(&mut set);
        let index_to_poly = set.into_iter().collect::<Box<[_]>>();

        // index_to_poly is mapping from i to (rotation, column_index, type), see [`Monomial`]
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

    // fold_transform will fold a polynomial expression P(f_1,...f_m, x_1,...,x_n)
    // and output P(f_1,...,f_m, x_1+r*y_1,...,x_n+r*y_n)
    // here mm = num_fixed+num_selectors
    // nn = num_advice
    pub(super) fn fold_transform(&self, mm: usize, nn: usize) -> Self {
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

    /// Transforms the current expression into a homogeneous expression with a potentially
    /// increased degree, based on the challenge.
    ///
    /// This function operates recursively and selectively increases the degree of the expression
    /// parts to make the overall expression homogeneous, i.e., of uniform degree.
    ///
    /// # Arguments
    ///
    /// * `new_challenge_index` - The index of the new challenge variable to be introduced for
    ///    degree adjustments.
    /// * `num_selector` & `num_fixed` Used to keep track of which columns are Fixed & Selector and
    ///    which are polynomials, which is important in terms of adding degree. Degree should only be
    ///    added for Advice columns. Advice column indexed start only after selectors & fixed indexed
    ///
    /// # Example
    /// ```math
    /// $$a\cdot b+c\rightarrow a\cdot b+c\cdot u$$
    ///```
    pub fn homogeneous(
        &self,
        new_challenge_index: usize,
        num_selector: usize,
        num_fixed: usize,
    ) -> HomogeneousExpression<F> {
        use Expression::*;

        fn multiply_by_u<F: PrimeField>(
            expr: Expression<F>,
            new_challenge_index: usize,
            degree: usize,
        ) -> Expression<F> {
            match degree.checked_sub(1) {
                Some(degree_sub_1) => multiply_by_u(
                    Expression::Challenge(new_challenge_index) * expr,
                    new_challenge_index,
                    degree_sub_1,
                ),
                None => expr,
            }
        }

        match self {
            Constant(constant) => (Constant(*constant), 0).into(),
            Polynomial(polynomial) => (
                Polynomial(*polynomial),
                if polynomial.is_advice(num_selector, num_fixed) {
                    1
                } else {
                    0
                },
            )
                .into(),
            Challenge(challenge) => (Challenge(*challenge), 1).into(),
            Sum(lhs, rhs) => {
                let HomogeneousExpression {
                    expr: lhs,
                    degree: lhs_degree,
                } = lhs.homogeneous(new_challenge_index, num_selector, num_fixed);
                let HomogeneousExpression {
                    expr: rhs,
                    degree: rhs_degree,
                } = rhs.homogeneous(new_challenge_index, num_selector, num_fixed);

                match lhs_degree.cmp(&rhs_degree) {
                    Ordering::Greater => (
                        lhs + multiply_by_u(rhs, new_challenge_index, lhs_degree - rhs_degree),
                        lhs_degree,
                    ),
                    Ordering::Less => (
                        multiply_by_u(lhs, new_challenge_index, rhs_degree - lhs_degree) + rhs,
                        rhs_degree,
                    ),
                    Ordering::Equal => (lhs + rhs, lhs_degree),
                }
                .into()
            }
            Product(lhs, rhs) => {
                let HomogeneousExpression {
                    expr: lhs,
                    degree: lhs_degree,
                } = lhs.homogeneous(new_challenge_index, num_selector, num_fixed);
                let HomogeneousExpression {
                    expr: rhs,
                    degree: rhs_degree,
                } = rhs.homogeneous(new_challenge_index, num_selector, num_fixed);

                (lhs * rhs, lhs_degree + rhs_degree).into()
            }
            Negated(expr) => {
                let HomogeneousExpression { expr, degree } =
                    expr.homogeneous(new_challenge_index, num_selector, num_fixed);
                (-expr, degree).into()
            }
            Scaled(expr, constant) => {
                let HomogeneousExpression { expr, degree } =
                    expr.homogeneous(new_challenge_index, num_selector, num_fixed);
                (Scaled(Box::new(expr), *constant), degree).into()
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Default)]
pub struct HomogeneousExpression<F: PrimeField> {
    pub expr: Expression<F>,
    degree: usize,
}

impl<F: PrimeField> ops::Deref for HomogeneousExpression<F> {
    type Target = Expression<F>;
    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

impl<F: PrimeField> From<(Expression<F>, usize)> for HomogeneousExpression<F> {
    fn from(value: (Expression<F>, usize)) -> Self {
        let (expr, degree) = value;
        Self { expr, degree }
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

#[cfg(test)]
mod tests {
    use std::array;

    use ff::PrimeField;
    // use pasta_curves::{Fp, pallas};
    use halo2_proofs::poly::Rotation;
    use halo2curves::pasta::{pallas, Fp};
    use tracing::*;
    use tracing_test::traced_test;

    use super::super::expression::*;

    #[traced_test]
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

    #[traced_test]
    #[test]
    fn test_multi_polynomial_homogeneous() {
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

    #[traced_test]
    #[test]
    fn test_homogeneous_simple() {
        use Expression::*;

        let expr1 = Polynomial(Query {
            index: 0,
            rotation: Rotation(0),
        }) + Constant(pallas::Base::from(1));

        let expr2 = Polynomial(Query {
            index: 0,
            rotation: Rotation(0),
        }) * Polynomial(Query {
            index: 1,
            rotation: Rotation(0),
        });

        let expr3 = expr1.clone() + expr2.clone();
        debug!("from {expr3}");
        assert_eq!(
            format!("{}", expr3.homogeneous(0, 0, 0).expr),
            "((r_0 * (Z_0 + (r_0 * 0x1))) + (Z_0 * Z_1))"
        );
    }

    #[traced_test]
    #[test]
    fn test_homogeneous() {
        let [a, b, c, d, e] = array::from_fn(|index| {
            Expression::<pallas::Base>::Polynomial(Query {
                index,
                rotation: Rotation(0),
            })
        });

        let expr = a.clone()
            + (a.clone() * b.clone())
            + (a.clone() * b.clone() * c.clone())
            + (a * b * c * d * e);

        debug!("from {expr}");

        let homogeneous = expr.homogeneous(0, 0, 0).expr;

        assert_eq!(
            format!("{}", homogeneous),
            "((r_0 * (r_0 * ((r_0 * ((r_0 * Z_0) + (Z_0 * Z_1))) + ((Z_0 * Z_1) * Z_2)))) + ((((Z_0 * Z_1) * Z_2) * Z_3) * Z_4))"
        );
    }
}
