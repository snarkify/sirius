use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, Fixed},
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

        pub fn from_different_field<D: PrimeField>(
            _input: D,
            _limb_width: NonZeroUsize,
            _n_limbs: NonZeroUsize,
        ) -> Result<Self, Error> {
            todo!("Implement and test the conversion of an element from another field")
        }

        pub fn into_bigint(&self, limb_width: usize) -> BigInt {
            self.limbs
                .iter()
                .rev()
                .fold(BigInt::zero(), |mut result, limb| {
                    result <<= limb_width;
                    result + f_to_nat(limb)
                })
        }

        pub fn get_limb(&self, limb_index: usize) -> Option<&F> {
            self.limbs.get(limb_index)
        }

        pub fn assign_advice(
            &self,
            ctx: &mut RegionCtx<'_, F>,
            annotation: &str,
            columns: &[Column<Advice>],
        ) -> Result<Vec<AssignedCell<F, F>>, Error> {
            if self.limbs.len() != columns.len() {
                return Err(Error::WrongColumnsSize {
                    limbs_count: self.limbs.len(),
                    columns_count: columns.len(),
                });
            }

            self.limbs
                .iter()
                .zip(columns.iter())
                .enumerate()
                .map(|(index, (val, col))| {
                    let annotation = format!("{annotation}_{index}");
                    ctx.assign_advice(|| &annotation, *col, Value::known(*val))
                        .map_err(|err| Error::AssignAdviceError { err, annotation })
                })
                .collect()
        }

        pub fn assign_fixed(
            &self,
            ctx: &mut RegionCtx<'_, F>,
            annotation: &str,
            columns: &[Column<Fixed>],
        ) -> Result<Vec<AssignedCell<F, F>>, Error> {
            if self.limbs.len() != columns.len() {
                return Err(Error::WrongColumnsSize {
                    limbs_count: self.limbs.len(),
                    columns_count: columns.len(),
                });
            }

            self.limbs
                .iter()
                .zip(columns.iter())
                .enumerate()
                .map(|(index, (val, col))| {
                    let annotation = format!("{annotation}_{index}");
                    ctx.assign_fixed(|| &annotation, *col, *val)
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
/// x, y - [`big_nat::BigNat`]
/// M - modulo
///
/// x = Sum_{i=0,...,N_x}[x[i] * w^i]
/// y = Sum_{i=0,...,N_x}[x[i] * w^i]
///
/// ```no_compile
/// x * y mod M = Sum_{i=0,...,N_x}[
///     Sum_{j=0,...,N_y}[
///         (x_i * y_j * w ^ k)
///     ]
/// ] mod M
/// ```
/// =>
/// ```no_compile
/// x * y mod M = Sum_{i=0,...,N_x}[
///     x_i * (Sum_{j=0,...,N_y}[y_j * w ^ k])
/// ] mod M
/// ```
/// => Thus, we first use `MainGateConfig::q_1` & `MainGateConfig::state[1..]`
/// to calculate the sum of `y_j` and put the result in `MainGateConfig::input`.
///
/// Then, we take the `MainGateConfig::input` and add
/// it to x_0 in `MainGateConfig::state[0]` and put it into
/// `MainGateConfig::output`.
///
/// Let's call this step [`MultStep`]. It occupies one line and allows
/// count one operand from the total amount.
///
/// Then we will collect all the steps from each line and add them up.
/// `MainGateConfig::state` & `MainGateConfig::output` will be used for this purpose
///
/// Let's call this step [`AggregationStep`]
pub struct BigNatMulModChip<F: ff::PrimeField, const T: usize> {
    main_gate: MainGate<F, T>,
}

pub enum Error {}

impl<F: ff::PrimeField, const T: usize> BigNatMulModChip<F, T> {
    // FIXME T to `T-1`
    /// Gives the columns to be used for the [`MultStep`] view.
    /// Depending on the passed index it takes different
    /// elements of the `lhs` operand
    fn get_mult_step(&self, _lhs_index: usize) -> MultStep<T> {
        todo!("Take the required columns from the main gate config")
    }

    // FIXME T to `T-1`
    /// Gives the columns to be used for the [`AggregationStep`] view.
    fn get_aggregation_step(&self) -> AggregationStep<T> {
        todo!("Take the required columns from the main gate config")
    }

    pub fn mult_mod(
        &self,
        _ctx: &mut RegionCtx<'_, F>,
        _lhs: BigInt,
        _rhs: BigInt,
    ) -> Result<BigInt, Error> {
        todo!(
            "
            1. Convert lhs,rhs from `BigInt` to the `BigNat`
            2. For each limb of lhs form MultStep and advice all needed params
            3. Aggregate results of `MultStep` in `AggregationStep`
            4. Don't forget to add checks for equality between MultStep results and what is in the AggregationStep input

            TODO Consider how to work with the module in intermediate steps
        "
        )
    }
}

/// Represents columns for multiplication step of [`BigNatMulModChip`]
///
/// x[i] * Sum_{j=0,..,N_y}[y[j] * W^j]
pub struct MultStep<'l, const RHS_LIMBS_COUNT: usize> {
    // x_i
    lhs: &'l Column<Advice>,
    // y_j where j = 0,..,N_y
    rhs: &'l [Column<Advice>; RHS_LIMBS_COUNT],
    // w_^j where j = 0,..,N_y
    power_term: &'l [Column<Fixed>; RHS_LIMBS_COUNT],
    // Sum_{j=0,..,N_y}[y[j] * W^j]
    intermediate_result: &'l Column<Advice>,
    /// x[i] * Sum_{j=0,..,N_y}[y[j] * W^j]
    output: &'l Column<Fixed>,
}

/// This step should be used to aggregate all [`MultStep`]
/// and add them into one [`Advice`] column.
pub struct AggregationStep<'l, const T: usize> {
    operands: &'l [Column<Advice>; T],
    /// x[i] * Sum_{j=0,..,N_y}[y[j] * W^j]
    output: &'l Column<Fixed>,
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
