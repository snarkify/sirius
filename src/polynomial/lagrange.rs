use std::{iter, num::NonZeroUsize};

use ff::PrimeField;

use crate::fft;

/// Lazy eval the values of the Lagrange polynomial for a cyclic subgroup of length `n` at
/// the `challenge` point
///
/// Panic, if challenge will be equal to any element of cyclic subgroup, because division by zero
///
///
/// # Mathematical Representation
///
/// ```math
/// L_i(X)=\frac{\omega^i}{n}\frac{X^k-1}{X-\omega^i}
/// ```
/// where {1, \omega, \omega^2, ..., \omega^n} - cyclic group
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

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use halo2_proofs::halo2curves::bn256::Fr;

    use super::*;

    fn to_nz(input: usize) -> NonZeroUsize {
        NonZeroUsize::new(input).unwrap()
    }

    #[test]
    fn basic_lagrange_test() {
        assert_eq!(
            iter_eval_lagrange_polynomials_for_cyclic_group(Fr::from(2u64), to_nz(4))
                .collect::<Vec<_>>(),
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
