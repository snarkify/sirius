use std::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    collections::{BTreeSet, HashSet},
    fmt,
    fmt::{Debug, Display},
    ops::{self, Add, Mul, Neg, Sub},
};

use halo2_proofs::{plonk::Expression as PE, poly::Rotation};
use serde::Serialize;

use crate::{ff::PrimeField, plonk::PlonkStructure, util::trim_leading_zeros};
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

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Default)]
pub struct QueryIndexContext {
    pub num_selectors: usize,
    pub num_fixed: usize,
    pub num_advice: usize,
    pub num_challenges: usize,
    pub num_lookups: usize,
}
impl<F: PrimeField> From<&PlonkStructure<F>> for QueryIndexContext {
    fn from(S: &PlonkStructure<F>) -> Self {
        Self {
            num_fixed: S.fixed_columns.len(),
            num_advice: S.num_advice_columns,
            num_selectors: S.selectors.len(),
            num_challenges: S.num_challenges,
            num_lookups: S.num_lookups(),
        }
    }
}

impl QueryIndexContext {
    pub fn num_fold_vars(self) -> usize {
        self.num_advice + self.num_lookups * 5
    }

    pub fn shift_advice_index(self, advice_poly_index: usize) -> usize {
        advice_poly_index + self.num_fold_vars()
    }

    pub fn shift_lookup_index(self, lookup_poly_index: usize) -> usize {
        lookup_poly_index + self.num_fold_vars()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub struct Query {
    pub index: usize,
    #[serde(serialize_with = "serialize_rotation")]
    pub rotation: Rotation,
}

pub enum QueryType {
    Selector,
    Fixed,
    Advice,
    Lookup,
}

impl Query {
    pub fn subtype(&self, ctx: &QueryIndexContext) -> QueryType {
        if self.index < ctx.num_selectors {
            QueryType::Selector
        } else if self.index < ctx.num_selectors + ctx.num_fixed {
            QueryType::Fixed
        } else if self.index < ctx.num_selectors + ctx.num_fixed + ctx.num_advice {
            QueryType::Advice
        } else if self.index
            < ctx.num_selectors + ctx.num_fixed + ctx.num_advice + (5 * ctx.num_lookups)
        {
            QueryType::Lookup
        } else {
            unreachable!("unknown index {} in {ctx:?}", self.index)
        }
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
            Expression::Challenge(index) => format!("r_{}", index),
            Expression::Negated(a) => format!("-{}", a),
            Expression::Sum(lhs, rhs) => {
                if let Expression::Negated(b) = &**rhs {
                    format!("{} - {}", lhs, b)
                } else {
                    format!("{} + {}", lhs, rhs)
                }
            }
            Expression::Product(lhs, rhs) => {
                let left = if let Expression::Sum(_, _) = &**lhs {
                    format!("({})", lhs.visualize())
                } else {
                    lhs.visualize()
                };
                let right = if let Expression::Sum(_, _) = &**rhs {
                    format!("({})", rhs.visualize())
                } else {
                    rhs.visualize()
                };
                format!("{} * {}", left, right)
            }
            Expression::Scaled(a, k) => {
                format!("{:?} * {}", trim_leading_zeros(format!("{:?}", k)), a)
            }
        }
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
    pub fn homogeneous(&self, ctx: &QueryIndexContext) -> HomogeneousExpression<F> {
        use Expression::*;
        let new_challenge_index = ctx.num_challenges;

        match self {
            Constant(constant) => HomogeneousExpression {
                expr: Constant(*constant),
                degree: 0,
            },
            Polynomial(polynomial) => HomogeneousExpression {
                expr: Polynomial(*polynomial),
                degree: match polynomial.subtype(ctx) {
                    QueryType::Advice | QueryType::Lookup => 1,
                    _other => 0,
                },
            },
            Expression::Challenge(challenge) => (Challenge(*challenge), 1).into(),
            Expression::Negated(expr) => {
                let HomogeneousExpression { expr, degree } = expr.homogeneous(ctx);
                (Expression::Negated(Box::new(expr)), degree).into()
            }
            Expression::Sum(lhs, rhs) => {
                let (
                    HomogeneousExpression {
                        expr: lhs,
                        degree: lhs_degree,
                    },
                    HomogeneousExpression {
                        expr: rhs,
                        degree: rhs_degree,
                    },
                ) = (lhs.homogeneous(ctx), rhs.homogeneous(ctx));

                match lhs_degree.cmp(&rhs_degree) {
                    Ordering::Greater => (
                        lhs + (rhs
                            * challenge_in_degree(
                                new_challenge_index,
                                lhs_degree.checked_sub(rhs_degree).unwrap(),
                            )),
                        lhs_degree,
                    ),
                    Ordering::Less => (
                        (lhs * challenge_in_degree(
                            new_challenge_index,
                            rhs_degree.checked_sub(lhs_degree).unwrap(),
                        )) + rhs,
                        rhs_degree,
                    ),
                    Ordering::Equal => (lhs + rhs, lhs_degree),
                }
                .into()
            }
            Expression::Product(lhs, rhs) => {
                let (
                    HomogeneousExpression {
                        expr: lhs,
                        degree: lhs_degree,
                    },
                    HomogeneousExpression {
                        expr: rhs,
                        degree: rhs_degree,
                    },
                ) = (lhs.homogeneous(ctx), rhs.homogeneous(ctx));

                (lhs * rhs, lhs_degree + rhs_degree).into()
            }
            Expression::Scaled(expr, constant) => {
                let HomogeneousExpression { expr, degree } = expr.homogeneous(ctx);

                (Scaled(Box::new(expr), *constant), degree).into()
            }
        }
    }

    pub fn degree(&self, ctx: &QueryIndexContext) -> usize {
        self.evaluate(
            &|_| 0,
            &|poly| match poly.subtype(ctx) {
                QueryType::Advice | QueryType::Lookup => 1,
                _other => 0,
            },
            &|_| 1,
            &|a| a,
            &|a, b| match a.cmp(&b) {
                Ordering::Equal | Ordering::Greater => a,
                Ordering::Less => b,
            },
            &|a, b| a + b,
            &|a, _| a,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Default)]
pub struct HomogeneousExpression<F: PrimeField> {
    pub expr: Expression<F>,
    pub degree: usize,
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

/// Multiply `Expression::Challenge(new_challenge_index)` by the `degree` time
pub fn challenge_in_degree<F: PrimeField>(
    new_challenge_index: usize,
    degree: usize,
) -> Expression<F> {
    let challenge = Expression::Challenge(new_challenge_index);
    let mut result = challenge.clone();

    for _ in 2..=degree {
        result = result * challenge.clone();
    }

    result
}

#[cfg(test)]
mod tests {
    use std::array;

    // use pasta_curves::{Fp, pallas};
    use halo2_proofs::poly::Rotation;
    use tracing::*;
    use tracing_test::traced_test;

    use super::super::expression::*;
    use crate::{
        ff::PrimeField,
        halo2curves::pasta::{pallas, Fp},
    };

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
        assert_eq!(
            expr.to_string(),
            "(Z_0 - 0x1) * (Z_0 - 0x1) + \"0x2\" * Z_0"
        );
    }

    #[traced_test]
    #[test]
    fn test_homogeneous_simple() {
        use Expression::*;

        let [a, b] = array::from_fn(|index| {
            Expression::<pallas::Base>::Polynomial(Query {
                index,
                rotation: Rotation(0),
            })
        });

        let expr1 = a.clone() + Constant(pallas::Base::from(1));
        let expr2 = a * b;

        let expr3 = expr1.clone() + expr2.clone();
        debug!("from {expr3}");
        assert_eq!(
            expr3
                .homogeneous(&QueryIndexContext {
                    num_advice: 2,
                    ..Default::default()
                })
                .expr
                .to_string(),
            "(Z_0 + 0x1 * r_0) * r_0 + Z_0 * Z_1"
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

        let homogeneous = expr
            .homogeneous(&QueryIndexContext {
                num_advice: 5,
                ..Default::default()
            })
            .expr;

        assert_eq!(
            homogeneous.to_string(),
            "((Z_0 * r_0 + Z_0 * Z_1) * r_0 + Z_0 * Z_1 * Z_2) * r_0 * r_0 + Z_0 * Z_1 * Z_2 * Z_3 * Z_4"
        );
    }
}
