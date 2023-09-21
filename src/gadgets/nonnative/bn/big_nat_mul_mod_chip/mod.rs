use std::{
    cmp, fmt, iter,
    num::NonZeroUsize,
    ops::Deref,
    ops::{Add, Div, Mul, Sub},
};

use bitter::{BitReader, LittleEndianReader};
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
    pub fn new(
        config: <Self as Chip<F>>::Config,
        limb_width: NonZeroUsize,
        limbs_count_limit: NonZeroUsize,
    ) -> Self {
        Self {
            main_gate: MainGate::new(config),
            limbs_count_limit,
            limb_width,
        }
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

        let (sum_cells, rhs_cells) = itertools::process_results(
            lhs.iter()
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

                    ctx.next();

                    Result::<_, Error>::Ok((sum_cell, rhs_cell))
                }),
            |iter| iter.unzip::<_, _, Vec<_>, Vec<_>>(),
        )?;

        let rhs_max_word =
            big_nat::nat_to_f::<F>(&big_nat::get_big_int_with_n_ones(self.limb_width.get()))
                .unwrap_or_default();

        Ok(SumContext {
            rhs: rhs_cells,
            res: OverflowingBigNat {
                cells: sum_cells,
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
        lhs_max_word: &F,
        rhs_max_word: &F,
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

        let min_limbs_count = F::from_u128(cmp::min(lhs_limbs_count, rhs_limbs_count) as u128);

        Ok(MultContext {
            lhs: lhs_cells.into_iter().flatten().collect(),
            rhs: rhs_cells.into_iter().flatten().collect(),
            res: OverflowingBigNat {
                cells: production_cells,
                max_word: min_limbs_count * rhs_max_word * lhs_max_word,
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
    /// |   ---    |   ---     |    ---     |  ---  |  ---  |      ---       |
    /// | state[0] | state[1]  |   q1[0]    | q1[1] |  q_o  |     output     |
    /// |   ---    |   ---     |    ---     |  ---  |  ---  |      ---       |
    /// |   ...    |   ...     |    ...     |  ...  |  ...  |      ...       |
    /// |   bn_i   | group_j^k | limb_shift |   1   |   -1  |  group_j^{k+1} |
    /// |   ...    |   ...     |    ...     |  ...  |  ...  |      ...       |
    /// ```
    /// where:
    /// - `bn_i` - i-th limb input big nat
    /// - `group_j^k` - group he belongs to.
    ///     - `j` calculated simply `i / limbs_per_group`
    ///     - `k` - is the intermediate index of the sum of the values of `k` limbs.
    ///             the largest `k` is the final value of an element of the group
    /// - `limb_shift` - (2 ^ limb_width) ^ limb_index_in_group`
    fn group_limbs(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bignat_cells: OverflowingBigNat<F>,
    ) -> Result<GroupedBigNat<F>, Error> {
        trace!("Group {} limbs: {:?}", bignat_cells.len(), bignat_cells);

        let limb_width = self.limb_width.get();
        let carry_bits = calc_carry_bits(&big_nat::f_to_nat(&bignat_cells.max_word), limb_width)?;
        let limbs_per_group = calc_limbs_per_group::<F>(carry_bits, limb_width)?;

        let group_count = bignat_cells.cells.len().sub(1).div(limbs_per_group).add(1);

        debug!(
            "group {bignat_cells:?}:
            limbs_count: {}
            limb_width: {limb_width},
            carry_bits: {carry_bits:?},
            limbs_per_group: {limbs_per_group},
            group_count: {group_count}",
            bignat_cells.cells.len()
        );

        let bignat_limb_column = &self.config().state[0];
        let bignat_limb_shift = &self.config().q_1[0];
        let current_group_value_column = &self.config().state[1];
        let current_group_selector = &self.config().q_1[1];

        let group_output_value_column = &self.config().out;
        let group_output_selector = &self.config().q_o;

        let limb_block = iter::successors(Some(F::ONE), |l| Some(l.double()))
            .nth(limb_width)
            .unwrap();

        let grouped = bignat_cells
            .iter()
            .enumerate() // add `limb_index`
            .chunks(limbs_per_group) // group limbs 
            .into_iter()
            .enumerate() // add `group_index`
            .map(|(group_index, limbs_for_group)| {
                // sum limbs from one group into one cell
                limbs_for_group
                    .zip(iter::successors(Some(F::ONE), |l| Some(limb_block * l))) // shift for every limbs in group
                    .try_fold(
                        None,
                        |mut prev_group_val, ((limb_index, original_limb_cell), shift)| {
                            let limb_cell = ctx.assign_advice_from(
                                || format!("{limb_index} limb for {group_index} group"),
                                *bignat_limb_column,
                                original_limb_cell,
                            )?;

                            ctx.assign_fixed(|| "shift for limb", *bignat_limb_shift, shift)?;

                            let mut new_group_value =
                                limb_cell.value().map(|f| *f) * Value::known(shift);

                            ctx.assign_fixed(
                                || format!("{group_index} group value selector for sum with {limb_index} limb"),
                                *current_group_selector,
                                F::ONE,
                            )?;

                            if let Some(prev_partial_group_val) = prev_group_val.take() {
                                let prev_group_val = ctx.assign_advice_from(
                                    || {
                                        format!(
                                            "{group_index} group value for sum with {limb_index} limb"
                                        )
                                    },
                                    *current_group_value_column,
                                    &prev_partial_group_val,
                                )?;

                                new_group_value = new_group_value + prev_group_val.value();
                            };

                            let group_val = ctx.assign_advice(
                                || format!("{limb_index} limb for {group_index} group"),
                                *group_output_value_column,
                                new_group_value,
                            )?;

                            ctx.assign_fixed(
                                || "selector for regroup output",
                                *group_output_selector,
                                -F::ONE,
                            )?;

                            ctx.next();

                            Result::<_, Error>::Ok(Some(group_val))
                        })
                        .transpose()
                        .expect("Unreachable, empty group not allowed")
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(GroupedBigNat {
            cells: grouped,
            max_word: bignat_cells.max_word,
        })
    }

    fn is_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: GroupedBigNat<F>,
        rhs: GroupedBigNat<F>,
    ) -> Result<(), Error> {
        debug!("equal check lhs {lhs:?}");
        debug!("equal check rhs {rhs:?}");

        let limb_width = self.limb_width.get();

        // FIXME
        let max_word_bn: BigInt = cmp::max(
            big_nat::f_to_nat(&lhs.max_word),
            big_nat::f_to_nat(&rhs.max_word),
        );
        let max_word: F = big_nat::nat_to_f(&max_word_bn).unwrap();

        debug!("max word: {max_word_bn}");

        let target_base_bn = BigInt::one() << limb_width;
        let target_base: F = big_nat::nat_to_f(&target_base_bn).expect("TODO");
        let inverted_target_base: F = Option::<F>::from(target_base.invert()).unwrap_or_default();

        let mut accumulated_extra = BigInt::zero();
        let carry_bits = calc_carry_bits(&max_word_bn, limb_width)?;
        debug!("carry_bits {carry_bits}");

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

        lhs.cells
            .into_iter()
            .zip_longest(rhs.cells.into_iter())
            .enumerate()
            .map(|(limb_index, cells)| -> Result<(), Error> {
                ctx.assign_fixed(|| format!("m_{limb_index} coeff"), *output_coeff, -F::ONE)?;

                // carry[i-1]
                ctx.assign_fixed(
                    || format!("carry_{limb_index} coeff"),
                    *carry_coeff,
                    F::ONE, // FIXME `target_base`? Or in hackmd error
                )?;

                ctx.assign_fixed(
                    || format!("selector lhs {limb_index} for calc dividend"),
                    *lhs_selector,
                    F::ONE,
                )?;

                ctx.assign_fixed(
                    || format!("selector rhs {limb_index} for calc dividend"),
                    *rhs_selector,
                    -F::ONE,
                )?;

                // max word
                let max_word =
                    ctx.assign_fixed(|| "max word for equal check", *max_word_column, max_word)?;

                ctx.assign_fixed(
                    || format!("carry_{limb_index} coeff"),
                    *carry_coeff,
                    -target_base,
                )?;

                // FIXME Not advice
                let m_i = big_nat::nat_to_f(&(&accumulated_extra % &target_base_bn)).expect("TODO");

                match cells {
                    EitherOrBoth::Both(lhs, rhs) => {
                        if limb_index == min_cells_len {
                            // -m_i
                            accumulated_extra += &max_word_bn;
                            ctx.assign_advice(
                                || format!("m_{limb_index}"),
                                *output_column,
                                Value::known(m_i),
                            )?;

                            accumulated_extra /= &target_base_bn;

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

                        // -rhs
                        let rhs_limb = ctx.assign_advice_from(
                            || format!("rhs {limb_index} for calc dividend"),
                            *rhs_column,
                            &rhs,
                        )?;

                        // -carry [i] * w
                        let carry_cell = ctx.assign_advice(
                            || format!("carry_{limb_index}"),
                            *carry_column,
                            (prev_carry + lhs_limb.value() - rhs_limb.value() + max_word.value())
                                * Value::known(&inverted_target_base),
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
                    }
                    EitherOrBoth::Right(rhs) => {
                        ctx.assign_advice_from(
                            || format!("rhs {limb_index} for check zero"),
                            *rhs_column,
                            &rhs,
                        )?;
                    }
                }

                ctx.next();

                Ok(())
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(())
    }

    /// From slice bytes, creates bit cells and verifies that they are indeed bits.
    /// Takes the first `expected_bits_count`.
    ///
    /// For every `k` rows looks like:
    /// ```markdown
    /// |   ---   |   ---   |  ---   |  ---  |  ---  |      ---       |
    /// |  input  |   q_i   | q1[1]  | q1[2] |  q_m  |     output     |
    /// |   ---   |   ---   |  ---   |  ---  |  ---  |      ---       |
    /// |   ...   |   ...   |  ...   |  ...  |  ...  |      ...       |
    /// |   b_i   |    1    |  b_i   |  b_i  |  -1   |  group_j^{k+1} |
    /// |   ...   |   ...   |  ...   |  ...  |  ...  |      ...       |
    /// ```
    /// Because:
    /// `input * q_i * q_m * q1[1] * q2[1] == 0` =>
    /// `b_i - b_i * b_i == 0`
    /// it's corrected only for `1` or `0`
    ///
    /// Bits represented in LE
    /// Return cells with bits
    fn check_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &[u8],
        expected_bits_count: NonZeroUsize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let bit_column = self.config().input;
        let bit_selector = self.config().q_i;

        let bit_square_multipliers_columns = self.config().state;
        let square_multipliers_coeff = self.config().q_m;

        // TODO Check BigEngian || LittleEndian
        let mut bits_repr = LittleEndianReader::new(bits);
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
            .collect::<Result<Vec<_>, Error>>()
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
        let bits_cells = self.check_bits(ctx, value_repr.as_ref(), expected_bits_count)?;

        let prev_chunk_sum_col = self.config().input;
        let prev_chunk_sum_selector = self.config().q_i;

        let bits_with_coeff =
            itertools::multizip((0.., bits_cells.iter(), get_power_of_two_iter::<F>()));

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

#[derive(Debug, Clone)]
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

#[derive(Debug)]
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

        let max_word_without_overflow: F =
            big_nat::nat_to_f(&big_nat::get_big_int_with_n_ones(self.limb_width.get()))
                .unwrap_or_default();

        let MultContext { res: left, .. } = self.assign_mult(
            ctx,
            lhs,
            rhs,
            &max_word_without_overflow,
            &max_word_without_overflow,
        )?;

        // q * m + r
        let MultContext {
            lhs: assigned_q,
            res: q_mul_m,
            ..
        } = self.assign_mult(
            ctx,
            q.limbs(),
            mod_bn.limbs(),
            &max_word_without_overflow,
            &max_word_without_overflow,
        )?;
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
        Ok(NonZeroUsize::new(carry_bits as usize).unwrap_or_else(|| {
            panic!(
                "
            Zero carry bits with max_word = {max_word} & limb_width = {limb_width}
            "
            )
        }))
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

fn get_power_of_two_iter<F: ff::PrimeField>() -> impl Iterator<Item = F> {
    iter::successors(Some(F::ONE), |l| Some(l.double()))
}

#[cfg(test)]
mod tests;
