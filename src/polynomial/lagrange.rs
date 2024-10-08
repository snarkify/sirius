use std::iter;

use crate::{ff::PrimeField, fft};

/// Returns an iterator over elements of a cyclic subgroup of a specified order in a given prime
/// field:
/// `{1, \omega, \omega^2, ..., \omega^n}` where `n = 2^log2(n)`
///
/// # Parameters
///
/// - `log_n` - `log2(n)`, where `n` - size of cyclic subgroup
///
/// # Returns
///
/// An iterator that yields elements of the cyclic subgroup
///
/// # Details
///
/// - The function first computes a generator of the cyclic subgroup using the [`fft::get_omega_or_inv`]
/// - The size of the cyclic subgroup `n` is computed as `2^log_n`.
/// - The iterator returns `n` elements, covering the full cycle of the cyclic subgroup
pub fn iter_cyclic_subgroup<F: PrimeField>(log_n: u32) -> impl Iterator<Item = F> {
    let generator: F = fft::get_omega_or_inv(log_n, false);

    iter::successors(Some(F::ONE), move |val| Some(*val * generator)).take(1 << log_n)
}

/// Lazy eval the values of the Lagrange polynomial for a cyclic subgroup of length `n` (`2.pow(log_n)`) at
/// the `challenge` point
///
/// You can look at [`fft::get_omega_or_inv`] to see how the target cyclic group is formed
///
/// # Parameters
///
/// - `log_n` - `log2(n)`, where `n` - size of cyclic subgroup
/// - `challenge` - eval Lagrange polynomials at this point
///
/// # Result
///
/// Iterator eval Lagrange polynomial values at the `challenge` point:
/// `L_0(challenge), L_1(challenge), ..., L_n(challenge)`
///
/// # Mathematical Representation
///
/// ```math
/// L_i(X)=\frac{\omega^i}{n}\frac{X^n-1}{X-\omega^i}
/// ```
/// where {1, \omega, \omega^2, ..., \omega^n} - cyclic group, check [`iter_cyclic_subgroup`] for
/// more details
pub fn iter_eval_lagrange_poly_for_cyclic_group<F: PrimeField>(
    X: F,
    lagrange_domain: u32,
) -> impl Iterator<Item = F> {
    let points_count = 2usize.pow(lagrange_domain);

    let inverted_n = F::from_u128(points_count as u128)
        .invert()
        .expect("safe because it's `2^log_n`");

    iter_cyclic_subgroup::<F>(lagrange_domain)
        .map(move |value| {
            let X_sub_value_inverted = X.sub(value).invert();
            let X_pow_n_sub_1 = X.pow([points_count as u64]) - F::ONE;

            // During the calculation, this part of the expression should be reduced to 1, but we
            // get 0/0 here, so we insert an explicit `if`.
            if X_pow_n_sub_1.is_zero_vartime() && X_sub_value_inverted.is_none().into() {
                F::ONE
            } else {
                value * inverted_n * (X_pow_n_sub_1 * X_sub_value_inverted.unwrap())
            }
        })
        .take(points_count)
}

/// This fn calculates vanishing polynomial $Z(X)$ from the formula $G(X)=F(\alpha)L_0(X)+K(X)Z(X)$
/// # Parameters
/// - `log_n` - logarithm of polynomial degree
/// - `point` - `x` - eval Lagrange polynomials at this point
/// # Result - x^n - 1
/// X^{2^log_n} - 1
/// -1 * X^0 + 0 * X^1 + ... + a * X^{2^log_n}
pub fn eval_vanish_polynomial<F: PrimeField>(degree: usize, point: F) -> F {
    point.pow([degree as u64]) - F::ONE
}

#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;
    use tracing_test::traced_test;

    use super::*;
    use crate::ff::Field;

    #[traced_test]
    #[test]
    fn correctness_for_cyclic_element() {
        const LOG_N: u32 = 8;

        let generator: Fr = fft::get_omega_or_inv(LOG_N, false);

        let n = 2usize.pow(LOG_N);

        iter::successors(Some(Fr::ONE), move |val| Some(*val * generator))
            .enumerate()
            .take(n)
            .for_each(|(j, w_j)| {
                iter_eval_lagrange_poly_for_cyclic_group(w_j, LOG_N)
                    .enumerate()
                    .for_each(|(i, L_i)| {
                        assert_eq!(L_i, if i == j { Fr::ONE } else { Fr::ZERO });
                    })
            });
    }

    #[test]
    fn basic_lagrange_test() {
        assert_eq!(
            iter_eval_lagrange_poly_for_cyclic_group(Fr::from(2u64), 2).collect::<Vec<_>>(),
            [
                "5472060717959818805561601436314318772137091100104008585924551046643952123908",
                "5472060717959818798949719980869953008325120142272090480018905346516323946831",
                "5472060717959818805561601436314318772137091100104008585924551046643952123903",
                "5472060717959818812173482891758684535949062057935926691830196746771580300976"
            ]
            .map(|f| Fr::from_str_vartime(f).unwrap())
        );
    }
}
