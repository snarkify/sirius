use std::{num::NonZeroUsize, ops::Div};

use ff::PrimeField;
use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column},
};
use num_bigint::BigInt;

use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};

pub mod big_nat {
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
}
use big_nat::BigNat;

pub enum MultModError {
    NotConsistentLimbWidth {
        lhs_limb_width: NonZeroUsize,
        rhs_limb_width: NonZeroUsize,
    },
    BigNatError(big_nat::Error),
}
impl From<big_nat::Error> for MultModError {
    fn from(value: big_nat::Error) -> Self {
        Self::BigNatError(value)
    }
}

/// Multiplication of two large natural numbers
pub struct BigNatMulModChip<F: ff::PrimeField, const T: usize> {
    main_gate: MainGate<F, T>,
    limb_width: NonZeroUsize,
    limbs_count_limit: NonZeroUsize,
}

impl<F: ff::PrimeField, const T: usize> BigNatMulModChip<F, T> {
    pub fn new(
        config: <Self as Chip<F>>::Config,
        limbs_count_limit: NonZeroUsize,
        limb_width: NonZeroUsize,
    ) -> Self {
        Self {
            main_gate: MainGate::new(config),
            limbs_count_limit,
            limb_width,
        }
    }

    pub fn lhs_column(&self) -> &Column<Advice> {
        todo!()
    }
    pub fn rhs_column(&self) -> &Column<Advice> {
        todo!()
    }
}

pub trait MultMod<INPUT, F: PrimeField> {
    fn mult_mod(
        &self,
        _ctx: &mut RegionCtx<'_, F>,
        lhs: INPUT,
        rhs: INPUT,
        modulus: INPUT,
    ) -> Result<INPUT, MultModError>;
}

impl<F: ff::PrimeField, const T: usize> MultMod<BigInt, F> for BigNatMulModChip<F, T> {
    #[allow(unused_variables)] // FIXME
    fn mult_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: BigInt,
        rhs: BigInt,
        modulus: BigInt,
    ) -> Result<BigInt, MultModError> {
        let to_bignat =
            |val| BigNat::<F>::from_bigint(val, self.limb_width, self.limbs_count_limit);

        let product = &lhs * &rhs;
        let quotient = &product / &modulus;
        let remainer = &product % &modulus;

        let lhs_nat = to_bignat(&lhs)?;
        let rhs_nat = to_bignat(&rhs)?;
        let mod_nat = to_bignat(&modulus)?;
        let quotient_nat = to_bignat(&quotient)?;
        let remainer_nat = to_bignat(&remainer)?;

        let assigned_lhs = lhs_nat.assign_advice(ctx, "lhs", self.lhs_column())?;
        let assigned_rhs = lhs_nat.assign_advice(ctx, "lhs", self.rhs_column())?;

        todo!()
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
