use halo2_proofs::circuit::Chip;

use crate::main_gate::{MainGate, MainGateConfig};

pub mod big_nat {
    use std::{io, iter, num::NonZeroUsize, ops::Not};

    use ff::PrimeField;
    use num_bigint::{BigInt, Sign};
    use num_traits::{identities::One, Zero};

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
            n_limbs: NonZeroUsize,
        ) -> Result<Self, Error> {
            let n_limbs = n_limbs.get();

            if input.bits() as usize > n_limbs * limb_width.get() {
                return Err(Error::TooBigBigint);
            }

            let mut nat = input.clone();
            let limb_mask = big_int_with_n_ones(limb_width.get());

            Self::from_limbs(
                iter::repeat_with(|| {
                    let r = &nat & &limb_mask;
                    nat >>= limb_width.get() as u32;
                    nat_to_f(&r).expect("TODO: Check safety")
                })
                .take(n_limbs),
                limb_width,
            )
        }

        pub fn into_bigint(self, limb_width: usize) -> BigInt {
            self.limbs
                .into_iter()
                .rev()
                .fold(BigInt::zero(), |mut result, limb| {
                    result <<= limb_width;
                    result + f_to_nat(&limb)
                })
        }

        pub fn get_limb(&self, limb_index: usize) -> Option<&F> {
            self.limbs.get(limb_index)
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
    fn big_int_with_n_ones(n: usize) -> BigInt {
        match n {
            0 => BigInt::zero(),
            n => (BigInt::one() << n) - 1,
        }
    }

    #[cfg(test)]
    mod tests {
        // TODO Add tests here for all cases
    }
}

/// Multiplication of two large natural numbers
///
/// Algorithm of multiplication:
pub struct BigNatMulModChip<F: ff::PrimeField, const T: usize> {
    main_gate: MainGate<F, T>,
}

impl<F: ff::PrimeField, const T: usize> BigNatMulModChip<F, T> {
    pub fn new(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            main_gate: MainGate::new(config),
        }
    }
}

impl<F: ff::PrimeField, const T: usize> Chip<F> for BigNatMulModChip<F, T> {
    type Config = MainGateConfig<T>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        self.main_gate.config()
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        plonk::{Circuit, Column, Instance},
    };

    use super::*;

    const DOUBLE_LIMBS: usize = 12;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig<const DOUBLE_LIMBS: usize> {
        pconfig: MainGateConfig<DOUBLE_LIMBS>,
        instance: Column<Instance>,
    }

    struct TestCircuit<F: ff::PrimeField + ff::PrimeFieldBits> {
        inputs: Vec<F>,
    }

    impl<F: ff::PrimeField + ff::PrimeFieldBits> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig<DOUBLE_LIMBS>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(_meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            todo!()
        }

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            todo!()
        }
    }
}
