pub mod expression;
pub mod graph_evaluator;
pub mod grouped_poly;
pub mod sparse;
pub mod univariate;

pub use expression::{ColumnIndex, Expression, Query, QueryType};

pub mod lagrange {
    use std::iter;

    use ff::PrimeField;

    use super::{expression::challenge_in_degree, Expression};

    trait GetCyclicSubGroup: PrimeField {
        fn get_generator() -> Self;

        fn get_cyclic_sub_group() -> impl Iterator<Item = Self> {
            iter::successors(Some(Self::ONE), |el| Some(*el * Self::get_generator()))
        }
    }

    struct Fraction<F> {
        numerator: Expression<F>,
        divider: Expression<F>,
    }

    fn get_lagrange_polynomials_for_cyclic_group<F: PrimeField + GetCyclicSubGroup>(
        challenge_index: usize,
        k: usize,
    ) -> impl Iterator<Item = Fraction<F>> {
        let X = Expression::Challenge(challenge_index);
        let X_pow_k = challenge_in_degree(challenge_index, k);
        let n = Expression::Constant(F::from_u128((k + 1) as u128));

        F::get_cyclic_sub_group()
            .map(|value| Expression::Constant(value))
            .map(move |value| Fraction {
                numerator: value.clone() * (X_pow_k.clone() - Expression::Constant(F::ONE)),
                divider: n.clone() * (X.clone() - value),
            })
            .take(k)
    }
}
