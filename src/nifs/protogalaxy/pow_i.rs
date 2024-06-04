use std::{iter, num::NonZeroU32};

use bitter::{BitReader, LittleEndianReader};
use ff::PrimeField;

/// Calculate pow_i relation from protogalaxy protocol
///
/// Not for public use, since it does not check that `i` can be fully represented by `t` number of
/// bits. In the case of an internal function, this is not necessary, due to the construction of
/// `n` in the module's public API.
fn pow_i<'l, F: PrimeField>(
    i: usize,
    t: NonZeroU32,
    challenges_powers: impl Iterator<Item = &'l F>,
) -> F {
    let bytes = i.to_le_bytes();
    let mut reader = LittleEndianReader::new(&bytes);

    iter::repeat_with(|| reader.read_bit().unwrap_or(false))
        .zip(challenges_powers)
        .map(|(b_j, beta_in_2j)| match b_j {
            true => *beta_in_2j,
            false => F::ONE,
        })
        .take(t.get() as usize)
        .reduce(|acc, coeff| acc * coeff)
        .unwrap()
}

/// Constructs an iterator yielding evaluated [`pow_i`] for indices from 0 to `n`.
///
/// # Params
/// - `log_n` - len of binary representation of `i`
/// - `challenge` - challenge for `pow_i` relation
///
/// # Mathematical Representation
///
/// For an integer `i` ranging from 0 to `n`, its binary representation `[i]_2 = (b_0, b_1, ..., b_{t-1})`,
/// and an input expression `challenge`, the polynomial term `pow_i` is defined as:
///
/// `beta` is `challenge`
/// ```math
/// pow_i(\boldsymbol{\beta}) =
///     pow_i(\beta, \cdots, \beta^{2^{t-1}}) =
///     \prod_{j=0}^{t-1}(1 - b_j + b_j \cdot \beta^{2^j})
/// ```
/// where `b_j` is the j-th bit of the binary representation of the integer `i`.
pub fn iter_eval_of_pow_i<F: PrimeField>(
    log_n: NonZeroU32,
    challenge: F,
) -> impl Iterator<Item = F> {
    // Eval here once, since each `pow_i` uses these values and pass them to the closure next
    let challenges = iter::successors(Some(challenge), |v| Some(v.square()))
        .take(log_n.get() as usize)
        .collect::<Box<[_]>>();

    let n = 2usize.pow(log_n.get());
    (0..n).map(move |i| pow_i(i, log_n, challenges.iter()))
}

#[cfg(test)]
mod test {
    use halo2_proofs::halo2curves::bn256::Fr;
    use tracing_test::traced_test;

    use super::*;

    fn to_nz_u32(input: u32) -> NonZeroU32 {
        NonZeroU32::new(input).unwrap()
    }

    fn to_challenges(input: Fr) -> Box<[Fr]> {
        iter::successors(Some(input), |val| Some(val.square()))
            .take(100)
            .collect()
    }

    #[traced_test]
    #[test]
    fn pow_5() {
        let challenges = to_challenges(Fr::one());
        assert_eq!(pow_i::<Fr>(5, to_nz_u32(3), challenges.iter()), Fr::one());
    }

    #[traced_test]
    #[test]
    fn iter_pow_i_test() {
        assert_eq!(
            iter_eval_of_pow_i::<Fr>(to_nz_u32(2), Fr::one()).collect::<Vec<Fr>>(),
            [Fr::one(), Fr::one(), Fr::one(), Fr::one()]
        );
    }

    #[traced_test]
    #[test]
    fn pow_7() {
        let challenges = to_challenges(Fr::one());
        // Test with i = 7 (binary 111) and t = 3
        assert_eq!(pow_i::<Fr>(7, to_nz_u32(3), challenges.iter()), Fr::one());
    }

    #[traced_test]
    #[test]
    fn pow_11() {
        let challenges = to_challenges(Fr::from(3));
        assert_eq!(
            pow_i::<Fr>(11, to_nz_u32(4), challenges.iter()),
            177_147.into()
        );
    }
}
