use std::iter;

use ff::PrimeField;

use super::{expression::challenge_in_degree, Expression};

pub struct Fraction<F> {
    numerator: Expression<F>,
    divider: Expression<F>,
}

pub fn get_lagrange_polynomials_for_cyclic_group<F: PrimeField>(
    challenge_index: usize,
    k: usize,
) -> impl Iterator<Item = Fraction<F>> {
    let X = Expression::Challenge(challenge_index);
    let X_pow_k = challenge_in_degree(challenge_index, k);
    let n = Expression::Constant(F::from_u128((k + 1) as u128));

    iter::successors(Some(Self::ONE), |el| Some(*el * F::ROOT_OF_UNITY))
        .map(|value| Expression::Constant(value))
        .map(move |value| Fraction {
            numerator: value.clone() * (X_pow_k.clone() - Expression::Constant(F::ONE)),
            divider: n.clone() * (X.clone() - value),
        })
        .take(k)
}
