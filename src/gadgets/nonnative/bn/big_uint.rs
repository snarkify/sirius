use std::{io, iter, num::NonZeroUsize, ops::Not};

use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{Advice, Column},
};
use log::*;
use num_bigint::BigUint as BigUintRaw;
use num_traits::{identities::One, Zero};

use crate::{error::Halo2PlonkError, main_gate::RegionCtx};

// A big natural number with limbs in field `F`
//
// Stores inside limbs of a certain length,
// created from [`num_bigint::BigUintRaw`] and
// allows access to certain limbs
//
// IMPORTANT: It is not an independent
// integer-type, but only a wrapper for
// storing a natural number with limbs.
#[derive(PartialEq, Debug)]
pub struct BigUint<F: PrimeField> {
    limbs: Vec<F>,
    width: NonZeroUsize,
}

impl<F: PrimeField> BigUint<F> {
    pub fn zero(limb_width: NonZeroUsize) -> Self {
        Self {
            limbs: vec![F::ZERO],
            width: limb_width,
        }
    }

    pub fn one(limb_width: NonZeroUsize) -> Self {
        Self {
            limbs: vec![F::ONE],
            width: limb_width,
        }
    }
}

#[derive(thiserror::Error, Debug, PartialEq, Eq)]
pub enum Error {
    // Too big bigint: try to increase the number of limbs or their width
    #[error("TODO")]
    TooBigBigint,
    #[error("The limb count check failed, it was expected to be less than {limit} and came up with {actual}")]
    LimbLimitReached { limit: NonZeroUsize, actual: usize },
    #[error("TODO")]
    EmptyLimbsNotAllowed,
    #[error("TODO")]
    AssignFixedError {
        annotation: String,
        err: Halo2PlonkError,
    },
    #[error("TODO")]
    AssignAdviceError {
        annotation: String,
        err: Halo2PlonkError,
    },
    #[error("TODO")]
    WrongColumnsSize {
        limbs_count: usize,
        columns_count: usize,
    },
    #[error("TODO")]
    LimbNotFound { limb_index: usize },
}

impl<F: ff::PrimeField> BigUint<F> {
    pub fn from_limbs(
        mut limbs_input: impl Iterator<Item = F>,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        let limbs = limbs_input
            .by_ref()
            .chain(iter::repeat(F::ZERO))
            .take(limbs_count.get())
            .collect::<Vec<_>>();

        let tail = limbs_input.collect::<Box<[_]>>();
        if tail.len() == 0 {
            Ok(Self {
                limbs,
                width: limb_width,
            })
        } else {
            error!("More limbs then expected count: {tail:?}");
            Err(Error::LimbLimitReached {
                limit: limbs_count,
                actual: tail.len() + limbs_count.get(),
            })
        }
    }

    pub fn from_u64(
        input: u64,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        // FIXME Simplify
        Self::from_biguint(&BigUintRaw::from(input), limb_width, limbs_count)
    }

    pub fn from_u128(
        input: u128,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        // FIXME Simplify
        Self::from_biguint(&BigUintRaw::from(input), limb_width, limbs_count)
    }

    // If the values in Cell are unknown, they will be filled in
    // Without any copy-constraint!
    pub fn from_assigned_cells(
        input: &[AssignedCell<F, F>],
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Option<Self>, Error> {
        if input.len() > limbs_count.get() {
            let err = Error::LimbLimitReached {
                actual: input.len(),
                limit: limbs_count,
            };
            error!("while `from_assigned_cells` limbs limit reached: {err:?}");
            return Err(err);
        }

        let limbs = input
            .iter()
            .map(|cell| *cell.value().map(|v| *v).unwrap())
            .map(|fv| {
                if let Some(fv) = fv {
                    let repr_len = fv.to_repr().as_ref().len();

                    if repr_len <= limb_width.get() {
                        Ok(Some(fv))
                    } else {
                        error!("Too big big int, repr_len is {repr_len} but limb width is {limb_width}");

                        Err(Error::TooBigBigint)
                    }
                } else {
                    Ok(None)
                }
            })
            .chain(iter::repeat_with(|| Ok(Some(F::ZERO))))
            .take(limbs_count.get())
            .collect::<Result<Option<Vec<_>>, _>>()?;

        limbs
            .map(|limbs| Self::from_limbs(limbs.into_iter(), limb_width, limbs_count))
            .transpose()
    }

    pub fn from_f(
        input: &F,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        Self::from_biguint(
            &BigUintRaw::from_bytes_le(input.to_repr().as_ref()),
            limb_width,
            limbs_count,
        )
    }

    pub fn from_biguint(
        input: &BigUintRaw,
        limb_width: NonZeroUsize,
        limbs_count: NonZeroUsize,
    ) -> Result<Self, Error> {
        let max_limbs_count = limbs_count.get();

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
            limbs_count,
        )
    }

    pub fn from_different_field<D: PrimeField>(
        _input: D,
        _limb_width: NonZeroUsize,
        _n_limbs: NonZeroUsize,
    ) -> Result<Self, Error> {
        todo!("Implement and test the conversion of an element from another field")
    }

    pub fn into_bigint(&self) -> num_bigint::BigUint {
        self.limbs
            .iter()
            .rev()
            .fold(BigUintRaw::zero(), |mut result, limb| {
                result <<= self.limb_width().get();
                result + f_to_nat(limb)
            })
    }

    pub fn into_f(&self) -> Option<F> {
        F::from_str_vartime(&self.into_bigint().to_str_radix(10))
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

    pub fn get_limb(&self, limb_index: usize) -> Result<&F, Error> {
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

pub fn nat_to_f<Scalar: ff::PrimeField>(n: &num_bigint::BigUint) -> Option<Scalar> {
    Scalar::from_str_vartime(&format!("{n}"))
}

fn write_be<F: PrimeField, W: io::Write>(f: &F, mut writer: W) -> io::Result<()> {
    f.to_repr()
        .as_ref()
        .iter()
        .rev()
        .try_for_each(|digit| writer.write_all(&[*digit]))
}

pub fn f_to_nat<Scalar: PrimeField>(f: &Scalar) -> num_bigint::BigUint {
    let mut s = Vec::new();
    write_be(f, &mut s).unwrap(); // f.to_repr().write_be(&mut s).unwrap();
    BigUintRaw::from_bytes_le(f.to_repr().as_ref())
}

// Calculate `2 ^ n - 1`
pub fn get_big_int_with_n_ones(n: usize) -> num_bigint::BigUint {
    match n {
        0 => BigUintRaw::zero(),
        n => (BigUintRaw::one() << n) - 1u8,
    }
}

fn get_max_word_mask_bits(limb_width: usize) -> usize {
    get_big_int_with_n_ones(limb_width).bits() as usize
}

#[cfg(test)]
mod tests {
    use std::mem;

    use ff::Field;
    use halo2curves::pasta::Fp;
    use test_log::test;

    use super::*;

    #[test]
    fn from_u64() {
        for input in [0, 256, u64::MAX / 2, u64::MAX] {
            let bn = BigUint::<Fp>::from_u64(
                input,
                NonZeroUsize::new(mem::size_of::<u64>() * 8).unwrap(),
                NonZeroUsize::new(4).unwrap(),
            )
            .unwrap();
            assert_eq!(bn.limbs_count().get(), 4, "Limbs > 1 at {input}");
            assert_eq!(
                bn.limbs(),
                &[Fp::from_u128(input.into()), Fp::ZERO, Fp::ZERO, Fp::ZERO,]
            );
            assert_eq!(bn.into_bigint(), BigUintRaw::from(input));
        }
    }

    #[test]
    fn from_u128() {
        for input in [u128::from(u64::MAX) + 1, u128::MAX / 2, u128::MAX] {
            let bn = BigUint::<Fp>::from_u128(
                input,
                NonZeroUsize::new(mem::size_of::<u128>() * 8).unwrap(),
                NonZeroUsize::new(4).unwrap(),
            )
            .unwrap();
            assert_eq!(bn.limbs_count().get(), 4, "Limbs > 1 at {input}");
            assert_eq!(
                bn.limbs(),
                &[Fp::from_u128(input), Fp::ZERO, Fp::ZERO, Fp::ZERO]
            );
            assert_eq!(bn.into_bigint(), BigUintRaw::from(input));
        }
    }

    #[test]
    fn from_two_limbs() {
        let input = BigUintRaw::from(u128::MAX) * BigUintRaw::from(u128::MAX);
        let bn = BigUint::<Fp>::from_biguint(
            &input,
            NonZeroUsize::new(mem::size_of::<u128>() * 8).unwrap(),
            NonZeroUsize::new(4).unwrap(),
        )
        .unwrap();
        assert_eq!(bn.limbs_count().get(), 4, "Limbs > 1 at {input}");
        assert_eq!(
            bn.limbs(),
            &[
                Fp::from_u128(0x0000000000000000000000000000000000000000000000000000000000000001),
                Fp::from_u128(0x00000000000000000000000000000000fffffffffffffffffffffffffffffffe),
                Fp::from_u128(0x0000000000000000000000000000000000000000000000000000000000000000),
                Fp::from_u128(0x0000000000000000000000000000000000000000000000000000000000000000)
            ]
        );

        assert_eq!(bn.into_bigint(), input);
    }

    #[test]
    fn limbs_count_err() {
        let input = BigUintRaw::from(u128::MAX) * BigUintRaw::from(u128::MAX);
        let result_with_bn = BigUint::<Fp>::from_biguint(
            &input,
            NonZeroUsize::new(mem::size_of::<u64>() * 8).unwrap(),
            NonZeroUsize::new(1).unwrap(),
        );

        assert_eq!(result_with_bn, Err(Error::TooBigBigint));
    }

    #[test]
    fn limbs_limit_err() {
        let limbs_count = NonZeroUsize::new(50).unwrap();
        let result_with_bn = BigUint::<Fp>::from_limbs(
            iter::repeat(Fp::ZERO).take(100),
            NonZeroUsize::new(mem::size_of::<u64>() * 8).unwrap(),
            limbs_count,
        );

        assert_eq!(
            result_with_bn,
            Err(Error::LimbLimitReached {
                limit: limbs_count,
                actual: 100,
            })
        );
    }
}
