use std::{
    cmp, iter,
    num::NonZeroUsize,
    ops::Deref,
    ops::{Add, Div, Mul, Sub},
};

use bitter::{BigEndianReader, BitReader};
use ff::PrimeField;
use halo2_proofs::circuit::{AssignedCell, Chip, Value};
use itertools::{EitherOrBoth, Itertools};
use log::*;
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};

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
    WhileAssignSumPart(halo2_proofs::plonk::Error),
    WhileAssignProdPart(halo2_proofs::plonk::Error),
    WhileAssignSelector(halo2_proofs::plonk::Error),
    WhileConstraintEqual(halo2_proofs::plonk::Error),
    WhileAssignForRegroup(halo2_proofs::plonk::Error),
    // TODO
    CarryBitsCalculate,
}
impl From<big_nat::Error> for Error {
    fn from(value: big_nat::Error) -> Self {
        Self::BigNat(value)
    }
}

/// Multiplication of two large natural numbers by mod
#[derive(Debug)]
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

    /// Assign result of sum of `lhs` & `rhs` without handle carry
    ///
    /// For every `k` rows looks like:
    /// ```markdown
    /// |   ---    |   ---    |  ---  |  ---  |  ---  |  ---   |
    /// | state[0] | state[1] | q1[0] | q1[1] |  q_o  | output |
    /// |   ---    |   ---    |  ---  |  ---  |  ---  |  ---   |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...   |
    /// |   lhs_0  |   rhs_0  |   1   |   1   |  -1   |  s_0   |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...   |
    /// |   lhs_i  |   rhs_j  |   1   |   1   |  -1   |  s_i   |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...   |
    /// |   lhs_l  |   rhs_l  |   1   |   1   |  -1   |  s_l   |
    /// |   ...    |   ...    |  ...  |  ...  |  ...  |  ...   |
    /// ```
    /// where:
    /// - `n` - lhs limbs count
    /// - `m` - rhs limbs count
    /// - `l` - min(n, m)
    /// - `s_i = lhs_i + rhs_i` where i in [0..l]
    ///
    /// The function also returns unchanged the remaining multipliers
    /// from the larger summand.
    fn assign_sum(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &OverflowingBigNat<F>,
        rhs: &OverflowingBigNat<F>,
    ) -> Result<OverflowingBigNat<F>, Error> {
        let lhs_column = &self.config().state[0];
        let rhs_column = &self.config().state[1];

        let lhs_selector = &self.config().q_1[0];
        let rhs_selector = &self.config().q_1[1];

        let sum_column = &self.config().out;
        let sum_selector = &self.config().q_o;

        let cells = lhs
            .iter()
            .zip_longest(rhs.iter())
            .map(|value| {
                let sum_cell = match value {
                    EitherOrBoth::Both(lhs, rhs) => {
                        ctx.assign_advice_from(|| "lhs", *lhs_column, lhs)
                            .map_err(Error::WhileAssignSumPart)?;

                        ctx.assign_fixed(|| "lhs_q_1", *lhs_selector, F::ONE)
                            .map_err(Error::WhileAssignSelector)?;

                        let rhs_cell = ctx
                            .assign_advice_from(|| "rhs", *rhs_column, rhs)
                            .map_err(Error::WhileAssignSumPart)?;

                        ctx.assign_fixed(|| "rhs_q_1", *rhs_selector, F::ONE)
                            .map_err(Error::WhileAssignSelector)?;

                        ctx.assign_fixed(|| "sum_q_o", *sum_selector, -F::ONE)
                            .map_err(Error::WhileAssignSelector)?;

                        ctx.assign_advice(
                            || "sum",
                            *sum_column,
                            lhs.value().copied().add(rhs_cell.value()),
                        )
                        .map_err(Error::WhileAssignSumPart)?
                    }
                    EitherOrBoth::Left(lhs) => lhs.clone(),
                    EitherOrBoth::Right(rhs) => rhs.clone(),
                };

                ctx.next();

                Ok(sum_cell)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        Ok(OverflowingBigNat {
            cells,
            max_word: lhs.max_word + rhs.max_word,
        })
    }

    /// Assign result of multiplication of `lhs` & `rhs` without handle carry
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
    fn assign_mult(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &BigInt,
        rhs: &BigInt,
    ) -> Result<OverflowingBigNat<F>, Error> {
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
                    ctx.assign_advice_from(
                        || "prev_prod_part",
                        *prev_part_column,
                        &prev_partial_result,
                    )
                    .map_err(Error::WhileAssignProdPart)?;

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

        let max_word = big_nat::get_big_int_with_n_ones(self.limb_width.get());

        Ok(OverflowingBigNat {
            cells: production_cells,
            max_word: big_nat::nat_to_f(&(&max_word * &max_word)).unwrap(),
        })
    }

    /// Re-group limbs of `BigNat`
    ///
    /// This function performs re-grouping limbs
    /// With [`calc_limbs_per_group`] we calculate how many
    /// limbs will fit in one group, given that the current
    /// limbs are merged into new limbs. The result is wrapped
    /// in [`GroupedBigNat`]
    ///
    /// For every `k` rows looks like:
    /// ```markdown
    /// |   ---    |   ---     |  ---   |  ---  |  ---  |      ---       |
    /// | state[0] | state[1]  | q1[1]  | q1[2] |  q_o  |     output     |
    /// |   ---    |   ---     |  ---   |  ---  |  ---  |      ---       |
    /// |   ...    |   ...     |  ...   |  ...  |  ...  |      ...       |
    /// |   bn_i   | group_j^k |   1    |   1   |   1   |  group_j^{k+1} |
    /// |   ...    |   ...     |  ...   |  ...  |  ...  |      ...       |
    /// ```
    /// where:
    /// - `bn_i` - i-th limb input big nat
    /// - `group_j^k` - group he belongs to.
    ///     - `j` calculated simply `i / limbs_per_group`
    ///     - `k` - is the intermediate index of the sum of the values of `k` limbs.
    ///             the largest `k` is the final value of an element of the group
    fn group_limbs(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bignat_cells: OverflowingBigNat<F>,
    ) -> Result<GroupedBigNat<F>, Error> {
        let limbs_per_group = calc_limbs_per_group::<F>(self.limb_width.get())?;

        let group_count = bignat_cells.len().sub(1).div(limbs_per_group.add(1));

        let mut grouped = vec![Option::<AssignedCell<F, F>>::None; group_count];

        let limb_block = iter::successors(Some(F::ONE), |l| Some(l.double()))
            .nth(self.limb_width.get())
            .unwrap();

        let bignat_limb_column = &self.config().state[0];
        let bignat_limb_shift = &self.config().q_1[0];
        let current_group_value_column = &self.config().state[1];
        let current_group_selector = &self.config().q_1[1];

        let group_output_value_column = &self.config().out;
        let group_output_selector = &self.config().q_o;

        let mut shift = F::ONE;
        for (index, original_limb_cell) in bignat_cells.iter().enumerate() {
            let group_index = index / limbs_per_group;

            if index % limbs_per_group == 0 {
                shift = F::ONE;
            }

            let limb_cell = ctx
                .assign_advice_from(
                    || format!("{index} limb for {group_index} group"),
                    *bignat_limb_column,
                    original_limb_cell,
                )
                .map_err(Error::WhileAssignForRegroup)?;

            ctx.assign_fixed(|| "shift for limb", *bignat_limb_shift, shift)
                .map_err(Error::WhileAssignForRegroup)?;

            let mut new_group_value = limb_cell.value().map(|f| *f) * Value::known(shift);

            if let Some(prev_partial_group_val) = grouped[group_index].take() {
                let prev_group_val = ctx
                    .assign_advice_from(
                        || format!("{group_index} group value for sum with {index} limb"),
                        *current_group_value_column,
                        &prev_partial_group_val,
                    )
                    .map_err(Error::WhileAssignForRegroup)?;

                ctx.assign_fixed(
                    || format!("{group_index} group value selector for sum with {index} limb"),
                    *current_group_selector,
                    F::ONE,
                )
                .map_err(Error::WhileAssignForRegroup)?;

                new_group_value = new_group_value + prev_group_val.value();
            };

            grouped[group_index] = Some(
                ctx.assign_advice(
                    || format!("{index} limb for {group_index} group"),
                    *group_output_value_column,
                    new_group_value,
                )
                .map_err(Error::WhileAssignForRegroup)?,
            );

            ctx.assign_fixed(
                || "selector for regroup output",
                *group_output_selector,
                -F::ONE,
            )
            .map_err(Error::WhileAssignForRegroup)?;

            shift.mul_assign(&limb_block);
            ctx.next();
        }

        Ok(GroupedBigNat {
            cells: grouped.into_iter().flatten().collect(),
            max_word: bignat_cells.max_word,
        })
    }

    fn is_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: GroupedBigNat<F>,
        rhs: GroupedBigNat<F>,
    ) -> Result<(), Error> {
        let limb_width = self.limb_width.get();

        // FIXME
        let max_word_bn: BigInt = cmp::max(
            big_nat::f_to_nat(&lhs.max_word),
            big_nat::f_to_nat(&rhs.max_word),
        );
        let max_word: F = big_nat::nat_to_f(&max_word_bn).unwrap();

        let target_base_bn = BigInt::one() << limb_width;
        let target_base: F = big_nat::nat_to_f(&target_base_bn).expect("TODO");
        let inverted_target_base: F = Option::<F>::from(target_base.invert()).unwrap_or_default();

        let mut accumulated_extra = BigInt::zero();
        let carry_bits = calc_carry_bits(limb_width)?;

        let lhs_column = &self.config().state[0];
        let lhs_selector = &self.config().q_1[0];

        let rhs_column = &self.config().state[1];
        let rhs_selector = &self.config().q_1[1];

        let carry_column = &self.config().input;
        let carry_coeff = &self.config().q_i;
        let mut prev_carry_cell = None;

        let max_word_column = &self.config().rc;

        let output_column = &self.config().out;
        let output_coeff = &self.config().q_o;

        let min_cells_len = cmp::min(lhs.cells.len(), rhs.cells.len());

        // TODO Separate last in lhs\rhs
        lhs.cells
            .into_iter()
            .zip_longest(rhs.cells.into_iter())
            .enumerate()
            .map(|(limb_index, cells)| -> Result<(), Error> {
                match cells {
                    EitherOrBoth::Both(lhs, rhs) => {
                        if limb_index == min_cells_len {
                            // -m_i
                            accumulated_extra += &max_word_bn;
                            // FIXME Not advice
                            let m_i = big_nat::nat_to_f(&(&accumulated_extra % &target_base_bn))
                                .expect("TODO");
                            ctx.assign_advice(
                                || format!("m_{limb_index}"),
                                *output_column,
                                Value::known(m_i),
                            )
                            .map_err(Error::WhileAssignForRegroup)?;
                            ctx.assign_fixed(
                                || format!("m_{limb_index} coeff"),
                                *output_coeff,
                                -F::ONE,
                            )
                            .map_err(Error::WhileAssignForRegroup)?;

                            accumulated_extra /= &target_base_bn;

                            // carry[i-1]
                            ctx.assign_fixed(
                                || format!("carry_{limb_index} coeff"),
                                *carry_coeff,
                                F::ONE, // FIXME `target_base`? Or in hackmd error
                            )
                            .map_err(Error::WhileAssignForRegroup)?;
                            if let Some(prev_carry_cell) = &prev_carry_cell {
                                ctx.assign_advice_from(
                                    || format!("carry_{limb_index}-1"),
                                    *carry_column,
                                    prev_carry_cell,
                                )
                                .map_err(Error::WhileAssignForRegroup)?;
                            }

                            ctx.next();

                            return Ok(());
                        }

                        // (carry[i-i] + lhs[i] - rhs[i] + max_word) / w = carry[i] * w + m[i]
                        //
                        // prev_carry + l[i] - o[i] - mw - (target_base * carry.num) - (accumulated_extra % target base) = 0
                        //
                        // (carry[i-i] + lhs[i] - rhs[i] + max_word) - carry[i] * w - m[i] =?= 0
                        //
                        // lhs = state[0]
                        // q_1[0] = 1
                        // rhs = state[1]
                        // q_1[1] = -1
                        // max_word = rc
                        // m[i] = output

                        // lhs
                        let lhs_limb = ctx
                            .assign_advice_from(
                                || format!("lhs {limb_index} for calc dividend"),
                                *lhs_column,
                                &lhs,
                            )
                            .map_err(Error::WhileAssignForRegroup)?;
                        ctx.assign_fixed(
                            || format!("selector lhs {limb_index} for calc dividend"),
                            *lhs_selector,
                            F::ONE,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;

                        // carry[i-1]
                        let prev_carry = if let Some(prev_carry_cell) = &prev_carry_cell {
                            ctx.assign_advice_from(
                                || format!("carry_{limb_index}-1"),
                                *carry_column,
                                prev_carry_cell,
                            )
                            .map_err(Error::WhileAssignForRegroup)?
                            .value()
                            .copied()
                        } else {
                            Value::known(F::ZERO)
                        };

                        // max word
                        let max_word = ctx
                            .assign_fixed(|| "max word for equal check", *max_word_column, max_word)
                            .map_err(Error::WhileAssignForRegroup)?;

                        // -rhs
                        let rhs_limb = ctx
                            .assign_advice_from(
                                || format!("rhs {limb_index} for calc dividend"),
                                *rhs_column,
                                &rhs,
                            )
                            .map_err(Error::WhileAssignForRegroup)?;
                        ctx.assign_fixed(
                            || format!("selector rhs {limb_index} for calc dividend"),
                            *rhs_selector,
                            -F::ONE,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;

                        // -carry [i] * w
                        let carry_cell = ctx
                            .assign_advice(
                                || format!("carry_{limb_index}"),
                                *carry_column,
                                (prev_carry + lhs_limb.value() - rhs_limb.value()
                                    + max_word.value())
                                    * Value::known(&inverted_target_base),
                            )
                            .map_err(Error::WhileAssignForRegroup)?;
                        ctx.assign_fixed(
                            || format!("carry_{limb_index} coeff"),
                            *carry_coeff,
                            -target_base,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;

                        // -m_i
                        accumulated_extra += &max_word_bn;
                        // FIXME Not advice
                        let m_i = big_nat::nat_to_f(&(&accumulated_extra % &target_base_bn))
                            .expect("TODO");
                        ctx.assign_advice(
                            || format!("m_{limb_index}"),
                            *output_column,
                            Value::known(m_i),
                        )
                        .map_err(Error::WhileAssignForRegroup)?;

                        ctx.assign_fixed(
                            || format!("m_{limb_index} coeff"),
                            *output_coeff,
                            -F::ONE,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;

                        accumulated_extra /= &target_base_bn;

                        ctx.next();
                        prev_carry_cell =
                            Some(self.check_fits_in_bits(ctx, carry_cell, carry_bits)?);
                    }
                    EitherOrBoth::Left(lhs) => {
                        ctx.assign_advice_from(
                            || format!("lhs {limb_index} for calc dividend"),
                            *lhs_column,
                            &lhs,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;
                        ctx.assign_fixed(
                            || format!("selector lhs {limb_index} for check zero"),
                            *lhs_selector,
                            F::ONE,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;
                    }
                    EitherOrBoth::Right(rhs) => {
                        ctx.assign_advice_from(
                            || format!("rhs {limb_index} for check zero"),
                            *rhs_column,
                            &rhs,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;
                        ctx.assign_fixed(
                            || format!("selector lhs {limb_index} for check zero"),
                            *rhs_selector,
                            F::ONE,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;
                    }
                }

                ctx.next();

                Ok(())
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(())
    }

    // Is it `cell` value have less then `expected_bits_count` in bits represtion
    // Is it `b in [0, 1]`?
    // b * (1 - b) = 0 =>
    //     b - b ** 2 = 0 =>
    //     -1 * (b ** 2) + 1 * b = 0
    //
    // q_m = -1
    // s[0] = b
    // s[1] = b
    // input = b
    // q_i = 1
    fn check_fits_in_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        cell: AssignedCell<F, F>,
        expected_bits_count: NonZeroUsize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let value_repr = cell
            .value()
            .map(|v| v.to_repr())
            .unwrap()
            .unwrap_or_else(|| F::ZERO.to_repr());

        // proof here all bits in [0, 1]
        let bits = {
            let bit_column = self.config().input;
            let bit_selector = self.config().q_i;

            let bit_square_multipliers_columns = self.config().state;

            let square_multipliers_coeff = self.config().q_m;

            let mut bits_repr = BigEndianReader::new(value_repr.as_ref());
            iter::repeat_with(|| bits_repr.read_bit())
                .take(expected_bits_count.get())
                .enumerate()
                .map(|(index, bit)| {
                    let bit_cell = ctx
                        .assign_advice(
                            || format!("bit_{index}"),
                            bit_column,
                            Value::known(match bit {
                                Some(true) => F::ONE,
                                Some(false) | None => F::ZERO,
                            }),
                        )
                        .map_err(Error::WhileAssignForRegroup)?;
                    ctx.assign_fixed(
                        || format!("bit_square_multipliers_coeff {index}"),
                        bit_selector,
                        F::ONE,
                    )
                    .map_err(Error::WhileAssignForRegroup)?;

                    for col in bit_square_multipliers_columns.iter().take(2) {
                        ctx.assign_advice_from(|| format!("bit_{index}"), *col, &bit_cell)
                            .map_err(Error::WhileAssignForRegroup)?;
                    }
                    ctx.assign_fixed(
                        || format!("square_multipliers_coeff {index}"),
                        square_multipliers_coeff,
                        -F::ONE,
                    )
                    .map_err(Error::WhileAssignForRegroup)?;

                    ctx.next();

                    Ok(bit_cell)
                })
                .collect::<Result<Vec<_>, Error>>()?
        };

        let prev_chunk_sum_col = self.config().input;
        let prev_chunk_sum_selector = self.config().q_i;

        let bits_with_coeff = itertools::multizip((0.., bits.iter(), get_power_of_two_iter::<F>()));

        let state_q1_columns =
            itertools::multizip((self.config().state, self.config().q_1)).collect::<Box<[_]>>();

        let final_sum_cell = bits_with_coeff
            .chunks(state_q1_columns.len())
            .into_iter()
            .try_fold(None, |prev_chunk_sum, bit_cell_chunk| {
                let mut current_chunk_sum = bit_cell_chunk.zip(state_q1_columns.iter()).try_fold(
                    Value::known(F::ZERO),
                    |current_chunk_sum, ((bit_index, bit_cell, bit_coeff), (state_col, state_coeff))| {
                        let bit_cell = ctx
                            .assign_advice_from(
                                || format!("bit {bit_index} in sum"),
                                *state_col,
                                bit_cell,
                            )
                            .map_err(Error::WhileAssignForRegroup)?;

                        let bit_coeff_cell = ctx
                            .assign_fixed(
                                || format!("bit {bit_index} coeff in sum"),
                                *state_coeff,
                                bit_coeff,
                            )
                            .map_err(Error::WhileAssignForRegroup)?;

                        Result::<_, Error>::Ok(current_chunk_sum + (bit_cell.value().map(|f| *f) * bit_coeff_cell.value()))
                    },
                )?;

                if let Some(prev_chunk_sum) = prev_chunk_sum {
                    ctx.assign_fixed(|| "prev_chunk_sum_coeff", prev_chunk_sum_selector, F::ONE)
                        .map_err(Error::WhileAssignForRegroup)?;

                    let prev_chunk_sum = ctx
                        .assign_advice_from(
                            || "prev_chunk_sum",
                            prev_chunk_sum_col,
                            &prev_chunk_sum,
                        )
                        .map_err(Error::WhileAssignForRegroup)?;

                    current_chunk_sum = current_chunk_sum + prev_chunk_sum.value();
                }

                ctx.assign_fixed(|| "chunk_sum_coeff", self.config().q_o, -F::ONE)
                    .map_err(Error::WhileAssignForRegroup)?;

                let cell = ctx.assign_advice(|| "chunk_sum", self.config().out, current_chunk_sum)
                    .map_err(Error::WhileAssignForRegroup)?;

                ctx.next();

                Result::<_, Error>::Ok(Some(cell))
            })?
            .expect("Safe, because carry_bits != 0");

        ctx.constrain_equal(final_sum_cell.cell(), cell.cell())
            .map_err(Error::WhileAssignForRegroup)?;

        Ok(cell)
    }
}

struct OverflowingBigNat<F: ff::PrimeField> {
    cells: Vec<AssignedCell<F, F>>,
    max_word: F,
}
impl<F: ff::PrimeField> Deref for OverflowingBigNat<F> {
    type Target = [AssignedCell<F, F>];
    fn deref(&self) -> &Self::Target {
        self.cells.as_slice()
    }
}

struct GroupedBigNat<F: ff::PrimeField> {
    cells: Vec<AssignedCell<F, F>>,
    max_word: F,
}
impl<F: ff::PrimeField> Deref for GroupedBigNat<F> {
    type Target = [AssignedCell<F, F>];
    fn deref(&self) -> &Self::Target {
        self.cells.as_slice()
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

fn calc_carry_bits(limb_width: usize) -> Result<NonZeroUsize, Error> {
    // FIXME: Is `f64` really needed here
    // We can calculate `log2` for BigInt without f64
    let carry_bits = big_nat::get_big_int_with_n_ones(limb_width)
        .mul(BigInt::one() + BigInt::one())
        .to_f64()
        .ok_or(Error::CarryBitsCalculate)?
        .log2()
        .sub(limb_width as f64)
        .ceil()
        .add(0.1);

    if carry_bits <= usize::MAX as f64 {
        Ok(NonZeroUsize::new(carry_bits as usize).expect("TODO"))
    } else {
        Err(Error::CarryBitsCalculate)
    }
}

/// Get how many limbs must be grouped in one
///
/// We count how many bits are needed per carry in the worst case, and use the remaining bits for grouping
///
/// let `max_word = 2 ^ limb_width - 1` then
/// let `carry_bits = usize(ceil(log_2(max_word * 2) - limb_width) + 0.1) then
/// let `limbs_per_group = capacity - carry_bits / limb_width`
fn calc_limbs_per_group<F: PrimeField>(limb_width: usize) -> Result<usize, Error> {
    Ok((F::CAPACITY as usize - calc_carry_bits(limb_width)?.get()) / limb_width)
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

            let prod: Vec<AssignedCell<F, F>> = layouter
                .assign_region(
                    || "assign_mult",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        Ok(chip
                            .assign_mult(&mut region, &self.lhs, &self.rhs)
                            .unwrap()
                            .cells)
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
}

fn get_power_of_two_iter<F: ff::PrimeField>() -> impl Iterator<Item = F> {
    iter::successors(Some(F::ONE), |l| Some(l.double()))
}
