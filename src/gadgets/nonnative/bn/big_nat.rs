use std::{io, iter, num::NonZeroUsize, ops::Not};

use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{Advice, Column, Fixed},
};
use num_bigint::{BigInt, Sign};
use num_traits::{identities::One, Zero};

use crate::main_gate::RegionCtx;

// A big natural number with limbs in field `F`
//
// Stores inside limbs of a certain length,
// created from [`num_bigint::BigInt`] and
// allows access to certain limbs
//
// IMPORTANT: It is not an independent
// integer-type, but only a wrapper for
// storing a natural number with limbs.
pub struct BigNat<F: ff::PrimeField> {
    limbs: Vec<F>,
    width: NonZeroUsize,
}

pub enum Error {
    // Too big bigint: try to increase the number of limbs or their width
    TooBigBigint,
    ZeroNotAllowed,
    AssignFixedError {
        annotation: String,
        err: halo2_proofs::plonk::Error,
    },
    AssignAdviceError {
        annotation: String,
        err: halo2_proofs::plonk::Error,
    },
    WrongColumnsSize {
        limbs_count: usize,
        columns_count: usize,
    },
}

impl<F: ff::PrimeField> BigNat<F> {
    pub fn from_limbs(
        limbs: impl Iterator<Item = F>,
        limb_width: NonZeroUsize,
    ) -> Result<Self, Error> {
        let mut is_all_limbs_zero = true;
        let limbs = limbs
            .inspect(|v| is_all_limbs_zero &= bool::from(v.is_zero().not()))
            .collect::<Vec<_>>();

        if is_all_limbs_zero || limbs.is_empty() {
            Err(Error::ZeroNotAllowed)
        } else {
            Ok(Self {
                limbs,
                width: limb_width,
            })
        }
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

    pub fn get_limb(&self, limb_index: usize) -> Option<&F> {
        self.limbs.get(limb_index)
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

    /// TODO Allow partial assign
    pub fn assign_advice(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        annotation: &str,
        column: &Column<Advice>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        self.limbs
            .iter()
            .enumerate()
            .map(|(index, val)| {
                let annotation = format!("{annotation}_{index}");
                ctx.region
                    .assign_advice(|| &annotation, *column, index, || Value::known(*val))
                    .map_err(|err| Error::AssignAdviceError { err, annotation })
            })
            .collect()
    }

    /// TODO Allow partial assign
    pub fn assign_fixed(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        annotation: &str,
        column: &Column<Fixed>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        self.limbs
            .iter()
            .enumerate()
            .map(|(index, val)| {
                let annotation = format!("{annotation}_{index}");
                ctx.region
                    .assign_fixed(|| &annotation, *column, index, || Value::known(*val))
                    .map_err(|err| Error::AssignFixedError { err, annotation })
            })
            .collect()
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
    // TODO Add tests here for all cases
}

