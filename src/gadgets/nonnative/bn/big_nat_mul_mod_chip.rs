use std::{num::NonZeroUsize, ops::Mul};

use ff::PrimeField;
use halo2_proofs::circuit::{AssignedCell, Chip};
use log::*;
use num_bigint::BigInt;

use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};

use super::big_nat::{self, BigNat};

#[derive(Debug)]
pub enum Error {
    InvalidTableSize,
    NotConsistentLimbWidth {
        lhs_limb_width: NonZeroUsize,
        rhs_limb_width: NonZeroUsize,
    },
    BigNat(big_nat::Error),
    WhileAssignProdPart(halo2_proofs::plonk::Error),
    WhileAssignSelector(halo2_proofs::plonk::Error),
    WhileConstraintEqual(halo2_proofs::plonk::Error),
}
impl From<big_nat::Error> for Error {
    fn from(value: big_nat::Error) -> Self {
        Self::BigNat(value)
    }
}

/// Multiplication of two large natural numbers by mod
pub struct BigNatMulModChip<F: ff::PrimeField> {
    main_gate: MainGate<F, 2>,
    limb_width: NonZeroUsize,
    limbs_count_limit: NonZeroUsize,
}

impl<F: ff::PrimeField> BigNatMulModChip<F> {
    pub fn try_new(
        config: <Self as Chip<F>>::Config,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Result<Self, Error> {
        Ok(Self {
            main_gate: MainGate::new(config),
            limbs_count_limit,
            limb_width,
        })
    }

    pub fn to_bignat(&self, input: &BigInt) -> Result<BigNat<F>, Error> {
        Ok(BigNat::<F>::from_bigint(
            input,
            self.limb_width,
            self.limbs_count_limit,
        )?)
    }

    /// Assign result of multiplication of `lhs` & `rhs`
    ///
    /// This function performs multiplication and assigns the results of multiplication.
    ///
    /// For every `k` rows looks like:
    /// ```markdown
    /// |   ---    |   ---    |  ---  |  ---  |  ---  |  ---       |  ---   |
    /// | state[0] | state[1] |  q_m  |  q_o  |  q_i  | input      | output |
    /// |   ---    |   ---    |  ---  |  ---  |  ---  |  ---       |  ---   |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...       |  ...   |
    /// |   lhs_0  |   rhs_k  |   1   |   -1  |   1   |  0         |  p_k^0 |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...       |  ...   |
    /// |   lhs_i  |   rhs_j  |   1   |   -1  |   1   |  p_k^{l-1} |  p_k^l |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...       |  ...   |
    /// |   lhs_k  |   rhs_0  |   1   |   -1  |   1   |  p_k^{k-1} |  p_k   |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...       |  ...   |
    /// ```
    /// where:
    /// - `i + j = k`
    /// - `p_k^l` is the `l` part for the product coefficient `p_k`
    /// - `p_k^k == p_k`.
    ///
    /// Thus:
    /// `state[0] * state[1] * q_m[0] + input - output = 0`
    /// in other words
    /// `lhs_i * lhs_j * 1 + p_k^{l-1} - p_k^l = 0`
    ///
    /// Number of rows := `∑_{k=0,.,n+m−2} min(k, n−1) − max(0, k−m+1) + 1`
    /// where `n` - limbs count of `lhs`, `m` limbs cout of `rhs`
    ///
    /// Returns the cells that contain the product coefficients
    /// TODO: carry handling or check `p_k` < `F::MODULUS`
    /// TODO: ignore the leading zeros
    pub fn assign_mult(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &BigInt,
        rhs: &BigInt,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        info!("Assign mult of {lhs} to {rhs}");

        let lhs = self.to_bignat(lhs)?;
        let rhs = self.to_bignat(rhs)?;
        trace!("In BigNat form {lhs:?} * {rhs:?}");

        let lhs_column = &self.config().state[0];
        let rhs_column = &self.config().state[1];
        let prev_part_column = &self.config().input;
        let prev_part_selector = &self.config().q_i;

        let mult_selector = &self.config().q_m;
        let out_selector = &self.config().q_o;

        let prod_column = &self.config().out;

        let lhs_limbs_count = lhs.limbs_count().get();
        let rhs_limbs_count = rhs.limbs_count().get();

        let prod_limb_count = lhs_limbs_count + rhs_limbs_count - 1;
        let mut production_cells: Vec<Option<AssignedCell<F, F>>> = vec![None; prod_limb_count];

        for i in 0..lhs_limbs_count {
            for j in 0..rhs_limbs_count {
                let lhs_limb_cell = lhs.assign_advice(ctx, "lhs", lhs_column, i)?;
                trace!("Assign lhs[{i}] for {lhs_limb_cell:?} cell");

                let rhs_limb_cell = rhs.assign_advice(ctx, "rhs", rhs_column, j)?;
                trace!("Assign rhs[{j}] for {rhs_limb_cell:?} cell");

                let mut part_of_product = lhs_limb_cell.value().copied().mul(rhs_limb_cell.value());
                let k = i + j;
                trace!("Part of product[{k}] = {part_of_product:?}");

                if let Some(prev_partial_result) =
                    production_cells.get_mut(k).and_then(|c| c.take())
                {
                    let prev_partial_value = prev_partial_result.value().copied();
                    let prev_prod_part = ctx
                        .assign_advice(|| "prev_prod_part", *prev_part_column, prev_partial_value)
                        .map_err(Error::WhileAssignProdPart)?;
                    ctx.constrain_equal(prev_prod_part.cell(), prev_partial_result.cell())
                        .map_err(Error::WhileConstraintEqual)?;

                    ctx.assign_fixed(|| "selector", *prev_part_selector, F::ONE)
                        .map_err(Error::WhileAssignSelector)?;

                    trace!("Previous partial value: {prev_partial_value:?}");

                    part_of_product = part_of_product + prev_partial_value;
                }

                for (selector, v) in [(mult_selector, F::ONE), (out_selector, -F::ONE)] {
                    ctx.assign_fixed(|| "selector", *selector, v)
                        .map_err(Error::WhileAssignSelector)?;
                }

                production_cells[k] = Some(
                    ctx.assign_advice(|| "out_prod_part", *prod_column, part_of_product)
                        .map_err(Error::WhileAssignProdPart)?,
                );

                trace!("Current prod[{k}] part: {:?}", production_cells[k]);

                ctx.next();
            }
        }

        let production_cells = production_cells
            .into_iter()
            .flatten()
            .skip_while(|el| matches!(el.value().unwrap(), Some(value) if value.is_zero().into()))
            .collect::<Vec<_>>();

        assert_eq!(
            production_cells.len(),
            lhs_limbs_count + rhs_limbs_count - 1
        );

        info!(
            "Production cells: {:?}",
            production_cells
                .iter()
                .filter_map(|c| *c.value().unwrap())
                .collect::<Box<[_]>>()
        );

        Ok(production_cells)
    }
}

pub trait MultMod<INPUT, F: PrimeField> {
    fn mult_mod(
        &self,
        _ctx: &mut RegionCtx<'_, F>,
        lhs: INPUT,
        rhs: INPUT,
        modulus: INPUT,
    ) -> Result<INPUT, Error>;
}

impl<F: ff::PrimeField> MultMod<BigInt, F> for BigNatMulModChip<F> {
    #[allow(unused_variables)] // FIXME
    fn mult_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: BigInt,
        rhs: BigInt,
        modulus: BigInt,
    ) -> Result<BigInt, Error> {
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

        todo!()
    }
}

impl<F: ff::PrimeField> Chip<F> for BigNatMulModChip<F> {
    type Config = MainGateConfig<2>;
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
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, Column, Instance},
    };
    use num_traits::FromPrimitive;

    use super::*;

    const DOUBLE_LIMBS: usize = 12;

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<2>,
        output: Column<Instance>,
    }

    struct TestCircuit<F: ff::PrimeField + ff::PrimeFieldBits> {
        lhs: BigInt,
        rhs: BigInt,
        _p: PhantomData<F>,
    }

    impl<F: ff::PrimeField + ff::PrimeFieldBits> TestCircuit<F> {
        pub fn new(lhs: BigInt, rhs: BigInt) -> Self {
            Self {
                lhs,
                rhs,
                _p: PhantomData,
            }
        }
    }

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(Fp::S as usize) };
    const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    impl<F: ff::PrimeField + ff::PrimeFieldBits> Circuit<F> for TestCircuit<F> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!("without_witnesses")
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            let output = meta.instance_column();
            meta.enable_equality(output);

            Config {
                main_gate_config: MainGate::<F, 2>::configure(meta),
                output,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            trace!("Start synthesize");

            let chip = BigNatMulModChip::<F>::try_new(
                config.main_gate_config,
                LIMB_WIDTH,
                LIMBS_COUNT_LIMIT,
            )
            .unwrap();

            let prod = layouter
                .assign_region(
                    || "assign_mult",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        Ok(chip.assign_mult(&mut region, &self.lhs, &self.rhs).unwrap())
                    },
                )
                .unwrap();

            for (offset, limb) in prod.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.output, offset)?;
            }

            Ok(())
        }
    }

    use halo2curves::pasta::Fp;

    #[test_log::test]
    fn test_little_bn_mult() {
        let lhs = BigInt::from_u64(100).unwrap();
        let rhs = BigInt::from_u64(100).unwrap();

        let prod = BigNat::from_bigint(&(&lhs * &rhs), LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();

        const K: u32 = 10;
        let prover = match MockProver::run(
            K,
            &TestCircuit::<Fp>::new(lhs, rhs),
            vec![prod.limbs().to_vec()],
        ) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test_log::test]
    fn test_bn_mult() {
        let lhs: BigInt = BigInt::from_u64(256 * 2).unwrap() * 2;
        let rhs: BigInt = BigInt::from_u64(100).unwrap();
        let prod = &lhs * &rhs;

        info!("Expected {lhs} * {rhs} = {prod}");
        let prod = BigNat::<Fp>::from_bigint(&prod, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();

        trace!("Prod limbs: {prod:?}");

        const K: u32 = 10;
        let prover = match MockProver::run(
            K,
            &TestCircuit::<Fp>::new(lhs, rhs),
            vec![prod.limbs().to_vec()],
        ) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };

        assert_eq!(prover.verify(), Ok(()));
    }
}
