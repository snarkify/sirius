use std::{
    iter, mem,
    num::{NonZeroU32, NonZeroUsize},
    ops::Mul,
};

use bitter::{BitReader, LittleEndianReader};
use ff::PrimeField;
use tracing::*;

#[derive(Debug, thiserror::Error, PartialEq, Eq, Clone)]
pub enum Error {
    #[error("Input `t` is not enough for represent `i`")]
    TooLittleT { t: NonZeroU32, needed_t: NonZeroU32 },
}

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

/// Constructs an iterator yielding evaluated `pow_i` for indices from 0 to `n`.
///
/// # Params
/// - `t` - lenght of binary representation of `i`. If `t` is too small to represent `i`, then
///       [`PowError::TooLittleT`] will return.
/// - `n` - limit for `pow_i` relations
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
    n: NonZeroUsize,
    challenge: F,
) -> Result<impl Iterator<Item = F>, Error> {
    let representation_lenght = NonZeroU32::new(
        mem::size_of::<usize>()
            .mul(8)
            .saturating_sub((n.leading_zeros() + 1) as usize) as u32,
    )
    .expect("`leading_zeros` can't be greater then bits count");

    if log_n < representation_lenght {
        return Err(Error::TooLittleT {
            t: log_n,
            needed_t: representation_lenght,
        });
    }

    let challenges = iter::successors(Some(challenge), |v| Some(v.square()))
        .take(log_n.get() as usize)
        .collect::<Box<[_]>>();

    Ok((0..=n.get()).map(move |i| pow_i(i, log_n, challenges.iter())))
}

#[cfg(test)]
mod test {
    use std::ops::Sub;

    use halo2_proofs::halo2curves::bn256::Fr;
    use tracing_test::traced_test;

    use super::*;

    fn to_nz(input: usize) -> NonZeroUsize {
        NonZeroUsize::new(input).unwrap()
    }

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
            iter_eval_of_pow_i::<Fr>(to_nz_u32(2), to_nz(3), Fr::one())
                .unwrap()
                .collect::<Vec<Fr>>(),
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

    #[traced_test]
    #[test]
    fn too_little_t() {
        let too_little_t = to_nz_u32(mem::size_of::<usize>().mul(8).sub(1) as u32);
        assert_eq!(
            iter_eval_of_pow_i::<Fr>(too_little_t, to_nz(usize::MAX), Fr::one())
                .err()
                .unwrap(),
            Error::TooLittleT {
                t: too_little_t,
                needed_t: to_nz_u32(mem::size_of::<usize>().mul(8) as u32)
            }
        );
    }
}
