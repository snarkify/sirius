use std::{iter, num::NonZeroUsize};

use ff::PrimeField;

use crate::fft;

/// Lazy eval the values of the Lagrange polynomial for a cyclic subgroup of length `n` at
/// the `challenge` point
///
/// Panic, if challenge will be equal to any element of cyclic subgroup, because division by zero
pub fn iter_eval_lagrange_polynomials_for_cyclic_group<F: PrimeField>(
    challenge: F,
    n: NonZeroUsize,
) -> impl Iterator<Item = F> {
    let n = n.get();

    let generator: F = fft::get_omega_or_inv(n.ilog2(), false);
    let cyclic_subgroup = iter::successors(Some(F::ONE), move |val| Some(*val * generator));

    let inverted_n = F::from(n as u64).invert().unwrap();
    let X_pow_n_sub_1 = challenge.pow([n as u64]) - F::ONE;

    cyclic_subgroup
        .map(move |value| {
            (value * inverted_n) * (X_pow_n_sub_1 * (challenge - value).invert().unwrap())
        })
        .take(n)
}
