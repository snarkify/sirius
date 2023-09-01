use std::{fmt, io, iter, num::NonZeroUsize, ops::Not};

use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{Advice, Column},
};
use num_bigint::{BigInt, Sign};
use num_traits::{identities::One, Zero};

use crate::{main_gate::RegionCtx, Halo2PlonkError};

// A big natural number with limbs in field `F`
//
// Stores inside limbs of a certain length,
// created from [`num_bigint::BigInt`] and
// allows access to certain limbs
//
// IMPORTANT: It is not an independent
// integer-type, but only a wrapper for
// storing a natural number with limbs.
#[derive(PartialEq)]
pub struct BigNat<F: ff::PrimeField> {
    limbs: Vec<F>,
    width: NonZeroUsize,
}

impl<F: ff::PrimeField + fmt::Debug> fmt::Debug for BigNat<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BigNat")
            .field("limbs", &self.limbs)
            .field("width", &self.width)
            .finish()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    // Too big bigint: try to increase the number of limbs or their width
    TooBigBigint,
    ZeroLimbNotAllowed,
    AssignFixedError {
        annotation: String,
        err: Halo2PlonkError,
    },
    AssignAdviceError {
        annotation: String,
        err: Halo2PlonkError,
    },
    WrongColumnsSize {
        limbs_count: usize,
        columns_count: usize,
    },
    LimbNotFound {
        limb_index: usize,
    },
}

impl<F: ff::PrimeField> BigNat<F> {
    pub fn from_limbs(
        limbs: impl Iterator<Item = F>,
        limb_width: NonZeroUsize,
    ) -> Result<Self, Error> {
        let mut is_all_limbs_zero = true;
        let limbs = limbs
            .inspect(|v| is_all_limbs_zero &= bool::from(v.is_zero()))
            .collect::<Vec<_>>();

        if is_all_limbs_zero || limbs.is_empty() {
            Err(Error::ZeroLimbNotAllowed)
        } else {
            Ok(Self {
                limbs,
                width: limb_width,
            })
        }
    }

    pub fn from_u64(
        input: u64,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Result<Self, Error> {
        // FIXME Simplify
        Self::from_bigint(&BigInt::from(input), limb_width, limbs_count_limit)
    }

    pub fn from_u128(
        input: u128,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Result<Self, Error> {
        // FIXME Simplify
        Self::from_bigint(&BigInt::from(input), limb_width, limbs_count_limit)
    }

    pub fn from_bigint(
        input: &BigInt,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Result<Self, Error> {
        let max_limbs_count = limbs_count_limit.get();

        if input.bits() as usize > max_limbs_count * limb_width.get() {
            return Err(Error::TooBigBigint);
        }

        let mut nat = input.clone();
        let limb_mask = get_big_int_with_n_ones(limb_width.get());
        Self::from_limbs(
            iter::repeat_with(|| {
                nat.is_zero().not().then(|| {
                    let r = &nat & &limb_mask;
                    nat >>= limb_width.get() as u32;
                    nat_to_f(&r).expect("TODO: Check safety")
                })
            })
            .take(max_limbs_count)
            .map_while(|mut o| o.take()),
            limb_width,
        )
    }

    pub fn from_different_field<D: PrimeField>(
        _input: D,
        _limb_width: NonZeroUsize,
        _n_limbs: NonZeroUsize,
    ) -> Result<Self, Error> {
        todo!("Implement and test the conversion of an element from another field")
    }

    pub fn into_bigint(&self) -> BigInt {
        self.limbs
            .iter()
            .rev()
            .fold(BigInt::zero(), |mut result, limb| {
                result <<= self.limb_width().get();
                result + f_to_nat(limb)
            })
    }

    pub fn limbs(&self) -> &[F] {
        self.limbs.as_slice()
    }

    pub fn limb_width(&self) -> &NonZeroUsize {
        &self.width
    }

    pub fn limbs_count(&self) -> NonZeroUsize {
        NonZeroUsize::new(self.limbs.len()).unwrap()
    }

    pub fn get_max_word_mask_bits(&self) -> usize {
        get_max_word_mask_bits(self.width.get())
    }

    pub fn bits_count(&self) -> usize {
        self.width.get() * (self.limbs_count().get() - 1) + self.get_max_word_mask_bits()
    }

    fn get_limb(&self, limb_index: usize) -> Result<&F, Error> {
        self.limbs
            .get(limb_index)
            .ok_or(Error::LimbNotFound { limb_index })
    }

    pub fn assign_advice(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        annotation: &str,
        column: &Column<Advice>,
        limb_index: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let annotation = format!("{annotation}_{limb_index}");

        ctx.assign_advice(
            || &annotation,
            *column,
            Value::known(*self.get_limb(limb_index)?),
        )
        .map_err(|err| Error::AssignAdviceError {
            err: err.into(),
            annotation,
        })
    }
}

pub fn nat_to_f<Scalar: ff::PrimeField>(n: &BigInt) -> Option<Scalar> {
    Scalar::from_str_vartime(&format!("{n}"))
}

fn write_be<F: PrimeField, W: io::Write>(f: &F, mut writer: W) -> io::Result<()> {
    f.to_repr()
        .as_ref()
        .iter()
        .rev()
        .try_for_each(|digit| writer.write_all(&[*digit]))
}

pub fn f_to_nat<Scalar: PrimeField>(f: &Scalar) -> BigInt {
    let mut s = Vec::new();
    write_be(f, &mut s).unwrap(); // f.to_repr().write_be(&mut s).unwrap();
    BigInt::from_bytes_le(Sign::Plus, f.to_repr().as_ref())
}

// Calculate `2 ^ n - 1`
fn get_big_int_with_n_ones(n: usize) -> BigInt {
    match n {
        0 => BigInt::zero(),
        n => (BigInt::one() << n) - 1,
    }
}

fn get_max_word_mask_bits(limb_width: usize) -> usize {
    get_big_int_with_n_ones(limb_width).bits() as usize
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;
    use halo2curves::pasta::Fp;
    use test_log::test;

    #[test]
    fn from_u64() {
        for input in [1, 256, u64::MAX / 2, u64::MAX] {
            let bn = BigNat::<Fp>::from_u64(
                input,
                NonZeroUsize::new(mem::size_of::<u64>() * 8).unwrap(),
                NonZeroUsize::new(4).unwrap(),
            )
            .unwrap();
            assert_eq!(bn.limbs_count().get(), 1, "Limbs > 1 at {input}");
            assert_eq!(bn.limbs(), &[Fp::from_u128(input.into())]);
            assert_eq!(bn.into_bigint(), BigInt::from(input));
        }
    }

    #[test]
    fn from_u128() {
        for input in [u128::from(u64::MAX) + 1, u128::MAX / 2, u128::MAX] {
            let bn = BigNat::<Fp>::from_u128(
                input,
                NonZeroUsize::new(mem::size_of::<u128>() * 8).unwrap(),
                NonZeroUsize::new(4).unwrap(),
            )
            .unwrap();
            assert_eq!(bn.limbs_count().get(), 1, "Limbs > 1 at {input}");
            assert_eq!(bn.limbs(), &[Fp::from_u128(input)]);
            assert_eq!(bn.into_bigint(), BigInt::from(input));
        }
    }

    #[test]
    fn from_two_limbs() {
        let input = BigInt::from(u128::MAX) * BigInt::from(u128::MAX);
        let bn = BigNat::<Fp>::from_bigint(
            &input,
            NonZeroUsize::new(mem::size_of::<u128>() * 8).unwrap(),
            NonZeroUsize::new(4).unwrap(),
        )
        .unwrap();
        assert_eq!(bn.limbs_count().get(), 2, "Limbs > 1 at {input}");
        assert_eq!(
            bn.limbs(),
            &[
                Fp::from_u128(0x0000000000000000000000000000000000000000000000000000000000000001),
                Fp::from_u128(0x00000000000000000000000000000000fffffffffffffffffffffffffffffffe)
            ]
        );

        assert_eq!(bn.into_bigint(), input);
    }

    #[test]
    fn limbs_count_err() {
        let input = BigInt::from(u128::MAX) * BigInt::from(u128::MAX);
        let result_with_bn = BigNat::<Fp>::from_bigint(
            &input,
            NonZeroUsize::new(mem::size_of::<u64>() * 8).unwrap(),
            NonZeroUsize::new(1).unwrap(),
        );

        assert_eq!(result_with_bn, Err(Error::TooBigBigint));
    }
}
