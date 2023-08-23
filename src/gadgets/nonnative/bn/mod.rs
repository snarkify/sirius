use std::num::NonZeroUsize;

use ff::PrimeField;
use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column},
};
use num_bigint::BigInt;

use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};

pub mod big_nat;
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
