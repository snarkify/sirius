use std::{
    cmp, fmt, iter,
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

use crate::main_gate::{AssignAdviceFrom, MainGate, MainGateConfig, RegionCtx};

use super::big_nat::{self, BigNat};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("TODO")]
    InvalidTableSize,
    #[error("TODO")]
    NotConsistentLimbWidth {
        lhs_limb_width: NonZeroUsize,
        rhs_limb_width: NonZeroUsize,
    },
    #[error("TODO")]
    BigNat(#[from] big_nat::Error),
    #[error("TODO")]
    Halo2(#[from] halo2_proofs::plonk::Error),
    // TODO
    #[error("TODO")]
    CarryBitsCalculate,
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
    /// - `k` - max(n, m)
    /// - `s_i = lhs_i + rhs_i` where i in [0..l)
    /// - `s_i = lhs_i` where
    ///     - i in [l..k)
    ///     - assumed that `lhs` has more limbs
    fn assign_sum(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &OverflowingBigNat<F>,
        rhs: &[F],
    ) -> Result<SumContext<F>, Error> {
        let lhs_column = &self.config().state[0];
        let rhs_column = &self.config().state[1];

        let lhs_selector = &self.config().q_1[0];
        let rhs_selector = &self.config().q_1[1];

        let sum_column = &self.config().out;
        let sum_selector = &self.config().q_o;

        let mut rhs_cells = vec![];

        let cells = lhs
            .iter()
            .zip_longest(rhs.iter())
            .enumerate()
            .map(|(index, value)| {
                ctx.assign_fixed(|| "lhs_q_1", *lhs_selector, F::ONE)?;
                ctx.assign_fixed(|| "rhs_q_1", *rhs_selector, F::ONE)?;
                ctx.assign_fixed(|| "sum_q_o", *sum_selector, -F::ONE)?;

                let (lhs_cell, rhs_cell) = match value {
                    EitherOrBoth::Both(lhs, rhs) => (
                        ctx.assign_advice_from(|| "lhs", *lhs_column, lhs)?,
                        ctx.assign_advice_from(|| "rhs", *rhs_column, rhs)?,
                    ),
                    EitherOrBoth::Left(lhs_limb) => (
                        ctx.assign_advice_from(|| "lhs", *lhs_column, lhs_limb)?,
                        ctx.assign_advice_from(|| "rhs", *rhs_column, F::ZERO)?,
                    ),
                    EitherOrBoth::Right(rhs_limb) => (
                        ctx.assign_advice_from(|| "lhs", *lhs_column, F::ZERO)?,
                        ctx.assign_advice_from(|| "rhs", *rhs_column, rhs_limb)?,
                    ),
                };

                let sum_cell = ctx.assign_advice(
                    || "sum",
                    *sum_column,
                    lhs_cell.value().copied().add(rhs_cell.value()),
                )?;

                trace!("sum lhs cell by {index}: {lhs_cell:?}");
                trace!("sum rhs cell by {index}: {rhs_cell:?}");
                trace!("sum res cell by {index}: {sum_cell:?}");

                rhs_cells.push(rhs_cell);

                ctx.next();

                Ok(sum_cell)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let rhs_max_word =
            big_nat::nat_to_f::<F>(&big_nat::get_big_int_with_n_ones(self.limb_width.get()))
                .unwrap_or_default();

        Ok(SumContext {
            rhs: rhs_cells,
            res: OverflowingBigNat {
                cells,
                max_word: lhs.max_word + rhs_max_word,
            },
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
    fn assign_mult<'a>(
        &self,
        ctx: &mut RegionCtx<'a, F>,
        lhs: &[impl AssignAdviceFrom<'a, F> + Clone + fmt::Debug],
        rhs: &[impl AssignAdviceFrom<'a, F> + Clone + fmt::Debug],
    ) -> Result<MultContext<F>, Error> {
        trace!("mult ctx: {ctx:?}");
        trace!("mult lhs: {lhs:?}");
        trace!("mult rhs: {rhs:?}");

        let lhs_column = &self.config().state[0];
        let rhs_column = &self.config().state[1];
        let prev_part_column = &self.config().input;
        let prev_part_selector = &self.config().q_i;

        let mult_selector = &self.config().q_m;
        let out_selector = &self.config().q_o;

        let prod_column = &self.config().out;

        let lhs_limbs_count = lhs.len();
        let rhs_limbs_count = rhs.len();

        let prod_limb_count = lhs_limbs_count + rhs_limbs_count - 1;
        let mut production_cells: Vec<Option<AssignedCell<F, F>>> = vec![None; prod_limb_count];

        let mut lhs_cells: Vec<Option<AssignedCell<_, _>>> = vec![None; lhs_limbs_count];
        let mut rhs_cells: Vec<Option<AssignedCell<_, _>>> = vec![None; rhs_limbs_count];

        for (i, lhs_limb) in lhs.iter().enumerate() {
            for (j, rhs_limb) in rhs.iter().enumerate() {
                let lhs_limb_cell = ctx.assign_advice_from(
                    || format!("lhs limb {i}"),
                    *lhs_column,
                    lhs_limb.clone(),
                )?;

                trace!("Assign lhs[{i}] for {lhs_limb_cell:?} cell");

                let rhs_limb_cell = ctx.assign_advice_from(
                    || format!("rhs limb {j}"),
                    *rhs_column,
                    rhs_limb.clone(),
                )?;

                trace!("Assign rhs[{i}] for {rhs_limb_cell:?} cell");

                let mut part_of_product = lhs_limb_cell.value().copied().mul(rhs_limb_cell.value());
                let k = i + j;
                trace!("Part of product[{k}] = {part_of_product:?}");

                // TODO: Move this outside, for simplify '`assigned_cell` as input' case
                match lhs_cells[i] {
                    Some(ref cell) => {
                        trace!(
                            "Check prev lhs limb ({cell:?} is equal to new one {lhs_limb_cell:?}"
                        );
                        ctx.constrain_equal(cell.cell(), lhs_limb_cell.cell())?;
                    }
                    None => {
                        lhs_cells[i] = Some(lhs_limb_cell);
                    }
                }
                // TODO: Move this outside, for simplify '`assigned_cell` as input' case
                match rhs_cells[j] {
                    Some(ref cell) => {
                        trace!(
                            "Check prev rhs limb ({cell:?} is equal to new one {rhs_limb_cell:?}"
                        );
                        ctx.constrain_equal(cell.cell(), rhs_limb_cell.cell())?;
                    }
                    None => {
                        rhs_cells[j] = Some(rhs_limb_cell);
                    }
                }

                ctx.assign_fixed(|| "selector", *prev_part_selector, F::ONE)?;
                if let Some(prev_partial_result) =
                    production_cells.get_mut(k).and_then(|c| c.take())
                {
                    let prev_partial_value = prev_partial_result.value().copied();
                    ctx.assign_advice_from(
                        || "prev_prod_part",
                        *prev_part_column,
                        &prev_partial_result,
                    )?;

                    trace!("Previous partial value: {prev_partial_value:?}");

                    part_of_product = part_of_product + prev_partial_value;
                }

                ctx.assign_fixed(|| "mult selector", *mult_selector, F::ONE)?;
                ctx.assign_fixed(|| "out selector", *out_selector, -F::ONE)?;

                production_cells[k] =
                    Some(ctx.assign_advice(|| "out_prod_part", *prod_column, part_of_product)?);

                trace!("Current prod[{k}] part: {:?}", production_cells[k]);

                ctx.next();
            }
        }

        let production_cells = production_cells.into_iter().flatten().collect::<Vec<_>>();

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

        Ok(MultContext {
            lhs: lhs_cells.into_iter().flatten().collect(),
            rhs: rhs_cells.into_iter().flatten().collect(),
            res: OverflowingBigNat {
                cells: production_cells,
                max_word: big_nat::nat_to_f(&(&max_word * &max_word)).unwrap(),
            },
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
        let limb_width = self.limb_width.get();
        let carry_bits = calc_carry_bits(&big_nat::f_to_nat(&bignat_cells.max_word), limb_width)?;
        let limbs_per_group = calc_limbs_per_group::<F>(carry_bits, limb_width)?;

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

            let limb_cell = ctx.assign_advice_from(
                || format!("{index} limb for {group_index} group"),
                *bignat_limb_column,
                original_limb_cell,
            )?;

            ctx.assign_fixed(|| "shift for limb", *bignat_limb_shift, shift)?;

            let mut new_group_value = limb_cell.value().map(|f| *f) * Value::known(shift);

            ctx.assign_fixed(
                || format!("{group_index} group value selector for sum with {index} limb"),
                *current_group_selector,
                F::ONE,
            )?;
            if let Some(prev_partial_group_val) = grouped[group_index].take() {
                let prev_group_val = ctx.assign_advice_from(
                    || format!("{group_index} group value for sum with {index} limb"),
                    *current_group_value_column,
                    &prev_partial_group_val,
                )?;

                new_group_value = new_group_value + prev_group_val.value();
            };

            grouped[group_index] = Some(ctx.assign_advice(
                || format!("{index} limb for {group_index} group"),
                *group_output_value_column,
                new_group_value,
            )?);

            ctx.assign_fixed(
                || "selector for regroup output",
                *group_output_selector,
                -F::ONE,
            )?;

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
        let carry_bits = calc_carry_bits(&max_word_bn, limb_width)?;

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
                            )?;
                            ctx.assign_fixed(
                                || format!("m_{limb_index} coeff"),
                                *output_coeff,
                                -F::ONE,
                            )?;

                            accumulated_extra /= &target_base_bn;

                            // carry[i-1]
                            ctx.assign_fixed(
                                || format!("carry_{limb_index} coeff"),
                                *carry_coeff,
                                F::ONE, // FIXME `target_base`? Or in hackmd error
                            )?;
                            if let Some(prev_carry_cell) = &prev_carry_cell {
                                ctx.assign_advice_from(
                                    || format!("carry_{limb_index}-1"),
                                    *carry_column,
                                    prev_carry_cell,
                                )?;
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
                        let lhs_limb = ctx.assign_advice_from(
                            || format!("lhs {limb_index} for calc dividend"),
                            *lhs_column,
                            &lhs,
                        )?;
                        ctx.assign_fixed(
                            || format!("selector lhs {limb_index} for calc dividend"),
                            *lhs_selector,
                            F::ONE,
                        )?;

                        // carry[i-1]
                        let prev_carry = if let Some(prev_carry_cell) = &prev_carry_cell {
                            ctx.assign_advice_from(
                                || format!("carry_{limb_index}-1"),
                                *carry_column,
                                prev_carry_cell,
                            )?
                            .value()
                            .copied()
                        } else {
                            Value::known(F::ZERO)
                        };

                        // max word
                        let max_word = ctx.assign_fixed(
                            || "max word for equal check",
                            *max_word_column,
                            max_word,
                        )?;

                        // -rhs
                        let rhs_limb = ctx.assign_advice_from(
                            || format!("rhs {limb_index} for calc dividend"),
                            *rhs_column,
                            &rhs,
                        )?;
                        ctx.assign_fixed(
                            || format!("selector rhs {limb_index} for calc dividend"),
                            *rhs_selector,
                            -F::ONE,
                        )?;

                        // -carry [i] * w
                        let carry_cell = ctx.assign_advice(
                            || format!("carry_{limb_index}"),
                            *carry_column,
                            (prev_carry + lhs_limb.value() - rhs_limb.value() + max_word.value())
                                * Value::known(&inverted_target_base),
                        )?;
                        ctx.assign_fixed(
                            || format!("carry_{limb_index} coeff"),
                            *carry_coeff,
                            -target_base,
                        )?;

                        // -m_i
                        accumulated_extra += &max_word_bn;
                        // FIXME Not advice
                        let m_i = big_nat::nat_to_f(&(&accumulated_extra % &target_base_bn))
                            .expect("TODO");
                        ctx.assign_advice(
                            || format!("m_{limb_index}"),
                            *output_column,
                            Value::known(m_i),
                        )?;

                        ctx.assign_fixed(
                            || format!("m_{limb_index} coeff"),
                            *output_coeff,
                            -F::ONE,
                        )?;

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
                        )?;
                        ctx.assign_fixed(
                            || format!("selector lhs {limb_index} for check zero"),
                            *lhs_selector,
                            F::ONE,
                        )?;
                    }
                    EitherOrBoth::Right(rhs) => {
                        ctx.assign_advice_from(
                            || format!("rhs {limb_index} for check zero"),
                            *rhs_column,
                            &rhs,
                        )?;
                        ctx.assign_fixed(
                            || format!("selector lhs {limb_index} for check zero"),
                            *rhs_selector,
                            F::ONE,
                        )?;
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

            // TODO Check BigEngian || LittleEndian
            let mut bits_repr = BigEndianReader::new(value_repr.as_ref());
            iter::repeat_with(|| bits_repr.read_bit())
                .take(expected_bits_count.get())
                .enumerate()
                .map(|(index, bit)| {
                    let bit_cell = ctx.assign_advice(
                        || format!("bit_{index}"),
                        bit_column,
                        Value::known(match bit {
                            Some(true) => F::ONE,
                            Some(false) | None => F::ZERO,
                        }),
                    )?;
                    ctx.assign_fixed(
                        || format!("bit_square_multipliers_coeff {index}"),
                        bit_selector,
                        F::ONE,
                    )?;

                    for col in bit_square_multipliers_columns.iter().take(2) {
                        ctx.assign_advice_from(|| format!("bit_{index}"), *col, &bit_cell)?;
                    }
                    ctx.assign_fixed(
                        || format!("square_multipliers_coeff {index}"),
                        square_multipliers_coeff,
                        -F::ONE,
                    )?;

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
                            ?;

                        let bit_coeff_cell = ctx
                            .assign_fixed(
                                || format!("bit {bit_index} coeff in sum"),
                                *state_coeff,
                                bit_coeff,
                            )
                            ?;

                        Result::<_, Error>::Ok(current_chunk_sum + (bit_cell.value().map(|f| *f) * bit_coeff_cell.value()))
                    },
                )?;

                ctx.assign_fixed(|| "prev_chunk_sum_coeff", prev_chunk_sum_selector, F::ONE)
                    ?;

                if let Some(prev_chunk_sum) = prev_chunk_sum {
                    let prev_chunk_sum = ctx
                        .assign_advice_from(
                            || "prev_chunk_sum",
                            prev_chunk_sum_col,
                            &prev_chunk_sum,
                        )
                        ?;

                    current_chunk_sum = current_chunk_sum + prev_chunk_sum.value();
                }

                ctx.assign_fixed(|| "chunk_sum_coeff", self.config().q_o, -F::ONE)
                    ?;

                let cell = ctx.assign_advice(|| "chunk_sum", self.config().out, current_chunk_sum)
                    ?;

                ctx.next();

                Result::<_, Error>::Ok(Some(cell))
            })?
            .expect("Safe, because carry_bits != 0");

        ctx.constrain_equal(final_sum_cell.cell(), cell.cell())?;

        Ok(cell)
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct MultModResult<F: PrimeField> {
    quotient: Vec<AssignedCell<F, F>>,
    remainder: Vec<AssignedCell<F, F>>,
}

#[derive(Debug)]
pub struct MultContext<F: PrimeField> {
    lhs: Vec<AssignedCell<F, F>>,
    rhs: Vec<AssignedCell<F, F>>,
    res: OverflowingBigNat<F>,
}

pub struct SumContext<F: PrimeField> {
    rhs: Vec<AssignedCell<F, F>>,
    res: OverflowingBigNat<F>,
}

impl<F: ff::PrimeField> BigNatMulModChip<F> {
    pub fn mult_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &[AssignedCell<F, F>],
        rhs: &[AssignedCell<F, F>],
        modulus: &[AssignedCell<F, F>],
    ) -> Result<MultModResult<F>, Error> {
        // lhs * rhs = q * m + r

        let to_bn = |val| {
            big_nat::BigNat::from_assigned_cells(val, self.limb_width, self.limbs_count_limit)
        };

        let mod_bn = to_bn(modulus)?;

        let lhs_bi = to_bn(lhs)?.into_bigint();
        let rhs_bi = to_bn(rhs)?.into_bigint();
        let mod_bi = mod_bn.into_bigint();

        let q = self.to_bignat(&((&lhs_bi * &rhs_bi) / &mod_bi))?;
        let r = self.to_bignat(&((&lhs_bi * &rhs_bi) % &mod_bi))?;

        // lhs * rhs
        let MultContext { res: left, .. } = self.assign_mult(ctx, lhs, rhs)?;

        // q * m + r
        let MultContext {
            lhs: assigned_q,
            res: q_mul_m,
            ..
        } = self.assign_mult(ctx, q.limbs(), mod_bn.limbs())?;
        let SumContext {
            rhs: assigned_r,
            res: right,
        } = self.assign_sum(ctx, &q_mul_m, r.limbs())?;

        // q * m + r
        let grouped_left = self.group_limbs(ctx, left)?;
        let grouped_right = self.group_limbs(ctx, right)?;

        self.is_equal(ctx, grouped_left, grouped_right)?;

        Ok(MultModResult {
            quotient: assigned_q,
            remainder: assigned_r,
        })
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

fn calc_carry_bits(max_word: &BigInt, limb_width: usize) -> Result<NonZeroUsize, Error> {
    // FIXME: Is `f64` really needed here
    // We can calculate `log2` for BigInt without f64
    let carry_bits = max_word
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
fn calc_limbs_per_group<F: PrimeField>(
    carry_bits: NonZeroUsize,
    limb_width: usize,
) -> Result<usize, Error> {
    Ok((F::CAPACITY as usize - carry_bits.get()) / limb_width)
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Advice, Circuit, Column, Instance},
    };
    use halo2curves::pasta::Fp;
    use num_traits::FromPrimitive;

    use super::*;

    const DOUBLE_LIMBS: usize = 12;

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<2>,
        lhs: Column<Instance>,
        rhs: Column<Instance>,
        assigned_mult: Column<Instance>,
        assigned_sum: Column<Instance>,

        advice_lhs: Column<Advice>,
        advice_rhs: Column<Advice>,
    }

    struct TestCircuit<F: ff::PrimeField + ff::PrimeFieldBits> {
        _p: PhantomData<F>,
    }

    impl<F: ff::PrimeField + ff::PrimeFieldBits> TestCircuit<F> {
        pub fn new() -> Self {
            Self { _p: PhantomData }
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
            let advice_lhs = meta.advice_column();
            meta.enable_equality(advice_lhs);

            let advice_rhs = meta.advice_column();
            meta.enable_equality(advice_rhs);

            let lhs = meta.instance_column();
            meta.enable_equality(lhs);

            let rhs = meta.instance_column();
            meta.enable_equality(rhs);

            let assigned_mult = meta.instance_column();
            meta.enable_equality(assigned_mult);

            let assigned_sum = meta.instance_column();
            meta.enable_equality(assigned_sum);

            Config {
                lhs,
                rhs,
                advice_lhs,
                advice_rhs,
                assigned_mult,
                assigned_sum,
                main_gate_config: MainGate::<F, 2>::configure(meta),
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

            let (assigned_mult, assigned_sum): (Vec<AssignedCell<F, F>>, Vec<AssignedCell<F, F>>) =
                layouter
                    .assign_region(
                        || "assign_mult",
                        |region| {
                            let mut region = RegionCtx::new(region, 0);

                            let limbs_count_limit = LIMBS_COUNT_LIMIT.get();
                            let (lhs, rhs): (Vec<_>, Vec<_>) = (0..limbs_count_limit)
                                .map(|limb_index| {
                                    let res = (
                                        region
                                            .assign_advice_from_instance(
                                                || format!("lhs {limb_index}"),
                                                config.advice_lhs,
                                                config.lhs,
                                                limb_index,
                                            )
                                            .unwrap(),
                                        region
                                            .assign_advice_from_instance(
                                                || format!("rhs {limb_index}"),
                                                config.advice_rhs,
                                                config.rhs,
                                                limb_index,
                                            )
                                            .unwrap(),
                                    );

                                    region.next();

                                    res
                                })
                                .unzip();

                            Ok((
                                chip.assign_mult(&mut region, &lhs, &rhs).unwrap().res.cells,
                                chip.assign_sum(
                                    &mut region,
                                    &OverflowingBigNat {
                                        cells: lhs.clone(),
                                        max_word: big_nat::nat_to_f::<F>(
                                            &big_nat::get_big_int_with_n_ones(LIMB_WIDTH.get()),
                                        )
                                        .unwrap_or_default(),
                                    },
                                    &rhs.iter()
                                        .take(limbs_count_limit)
                                        .map(|c| *c.value().unwrap().unwrap_or(&F::ZERO))
                                        .collect::<Box<[_]>>(),
                                )
                                .unwrap()
                                .res
                                .cells,
                            ))
                        },
                    )
                    .unwrap();

            for (offset, limb) in assigned_mult.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.assigned_mult, offset)?;
            }

            for (offset, limb) in assigned_sum.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.assigned_sum, offset)?;
            }

            Ok(())
        }
    }

    fn mult_with_overflow<F: PrimeField>(lhs: &BigNat<F>, rhs: &BigNat<F>) -> BigNat<F> {
        let lhs_limbs_count = lhs.limbs().len();
        let rhs_limbs_count = rhs.limbs().len();

        let mut production_cells: Vec<Option<F>> =
            vec![None; lhs_limbs_count + rhs_limbs_count - 1];

        for (i, lhs_limb) in lhs.limbs().iter().enumerate() {
            for (j, rhs_limb) in rhs.limbs().iter().enumerate() {
                let k = i + j;
                production_cells[k] =
                    Some(production_cells[k].take().unwrap_or(F::ZERO) + (*lhs_limb * rhs_limb));
            }
        }

        BigNat::from_limbs(production_cells.into_iter().flatten(), LIMB_WIDTH).unwrap()
    }

    fn sum_with_overflow<F: PrimeField>(lhs: &BigNat<F>, rhs: &BigNat<F>) -> BigNat<F> {
        BigNat::from_limbs(
            lhs.limbs()
                .iter()
                .zip_longest(rhs.limbs().iter())
                .enumerate()
                .map(|(index, limbs)| {
                    let limb = match limbs {
                        EitherOrBoth::Both(lhs, rhs) => {
                            trace!("sum val lhs[{index}] = {lhs:?}");
                            trace!("sum val rhs[{index}] = {rhs:?}");
                            *lhs + rhs
                        }
                        EitherOrBoth::Left(lhs) => {
                            trace!("sum val rhs[{index}] = None");
                            trace!("sum val lhs[{index}] = {lhs:?}");
                            *lhs
                        }
                        EitherOrBoth::Right(rhs) => {
                            trace!("sum val rhs[{index}] = {rhs:?}");
                            trace!("sum val lhs[{index}] = None");
                            *rhs
                        }
                    };
                    trace!("calculated val res[{index}] = {limb:?}");
                    limb
                }),
            LIMB_WIDTH,
        )
        .unwrap()
    }

    #[test_log::test]
    fn test_bn() {
        let lhs = BigInt::from_u64(u64::MAX).unwrap() * BigInt::from_u64(100).unwrap();
        let rhs = BigInt::from_u64(u64::MAX).unwrap() * BigInt::from_u64(u64::MAX).unwrap();

        let lhs = BigNat::from_bigint(&lhs, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();
        let rhs = BigNat::from_bigint(&rhs, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();
        let prod = mult_with_overflow(&lhs, &rhs);
        log::info!("prod {prod:?}");
        let sum = sum_with_overflow(&lhs, &rhs);
        log::info!("sum {sum:?}");

        const K: u32 = 10;
        let ts = TestCircuit::<Fp>::new();
        let prover = match MockProver::run(
            K,
            &ts,
            vec![
                lhs.limbs().to_vec(),
                rhs.limbs().to_vec(),
                prod.limbs().to_vec(),
                sum.limbs().to_vec(),
            ],
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
