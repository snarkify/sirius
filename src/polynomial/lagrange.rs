use std::iter;

use ff::PrimeField;

use crate::fft;

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

    iter::successors(Some(F::ONE), move |val| Some(*val * generator))
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
pub fn iter_eval_lagrange_polynomials_for_cyclic_group<F: PrimeField>(
    challenge: F,
    log_n: u32,
) -> impl Iterator<Item = F> {
    let n = 2usize.pow(log_n);

    let inverted_n = F::from_u128(n as u128)
        .invert()
        .expect("safe because it's `2^log_n`");
    let X_pow_n_sub_1 = challenge.pow([n as u64]) - F::ONE;

    iter_cyclic_subgroup(log_n)
        .map(move |value: F| {
            let challenge_sub_value_inverted = challenge.sub(value).invert();

            // During the calculation, this part of the expression should be reduced to 1, but we
            // get 0/0 here, so we insert an explicit `if`.
            if X_pow_n_sub_1.is_zero_vartime() && challenge_sub_value_inverted.is_none().into() {
                F::ONE
            } else {
                value * inverted_n * (X_pow_n_sub_1 * challenge_sub_value_inverted.unwrap())
            }
        })
        .take(n)
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use halo2_proofs::halo2curves::bn256::Fr;
    use tracing_test::traced_test;

    use super::*;

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
                iter_eval_lagrange_polynomials_for_cyclic_group(w_j, LOG_N)
                    .enumerate()
                    .for_each(|(i, L_i)| {
                        assert_eq!(L_i, if i == j { Fr::ONE } else { Fr::ZERO });
                    })
            });
    }

    #[test]
    fn basic_lagrange_test() {
        assert_eq!(
            iter_eval_lagrange_polynomials_for_cyclic_group(Fr::from(2u64), 2).collect::<Vec<_>>(),
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
