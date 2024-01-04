use std::{
    cmp, fmt, iter,
    num::NonZeroUsize,
    ops::{Add, Div, Mul, Sub},
    ops::{Deref, Not},
};

use bitter::{BitReader, LittleEndianReader};
use ff::PrimeField;
use halo2_proofs::circuit::{AssignedCell, Chip, Value};
use itertools::{EitherOrBoth, Itertools};
use log::*;
use num_bigint::BigUint as BigUintRaw;
use num_traits::{One, ToPrimitive, Zero};

use crate::{
    main_gate::{AssignAdviceFrom, MainGate, MainGateConfig, RegionCtx},
    util,
};

use super::big_uint::{self, BigUint};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error(transparent)]
    BigUint(#[from] big_uint::Error),
    #[error(transparent)]
    Halo2(#[from] halo2_proofs::plonk::Error),
    #[error(
        "During the calculation of carry bits the number is converted to f64 and an error occurred"
    )]
    CarryBitsCalculate,
    #[error("Error while calculate limbs per group count")]
    ZeroLimbsPerGroup,
    #[error("Carry bits equal capacity of `Curve::Base`")]
    CarryBitsEqualCapacity,
}

pub const MAIN_GATE_T: usize = 4;

/// Multiplication of two large natural numbers by mod
#[derive(Debug)]
pub struct BigUintMulModChip<F: ff::PrimeField> {
    main_gate: MainGate<F, MAIN_GATE_T>,
    limb_width: NonZeroUsize,
    limbs_count_limit: NonZeroUsize,
}

impl<F: ff::PrimeField> BigUintMulModChip<F> {
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

    pub fn to_bignat(&self, input: &BigUintRaw) -> Result<BigUint<F>, Error> {
        Ok(BigUint::<F>::from_biguint(
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
    pub fn assign_sum<'a>(
        &self,
        ctx: &mut RegionCtx<'a, F>,
        lhs: &OverflowingBigUint<F>,
        rhs: &[impl AssignAdviceFrom<'a, F> + Clone + fmt::Debug],
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
                            ctx.assign_advice_from(|| "rhs", *rhs_column, rhs.clone())?,
                        ),
                        EitherOrBoth::Left(lhs_limb) => (
                            ctx.assign_advice_from(|| "lhs", *lhs_column, lhs_limb)?,
                            ctx.assign_advice_from(|| "rhs", *rhs_column, F::ZERO)?,
                        ),
                        EitherOrBoth::Right(rhs_limb) => (
                            ctx.assign_advice_from(|| "lhs", *lhs_column, F::ZERO)?,
                            ctx.assign_advice_from(|| "rhs", *rhs_column, rhs_limb.clone())?,
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
            big_uint::nat_to_f::<F>(&big_uint::get_big_int_with_n_ones(self.limb_width.get()))
                .unwrap_or_default();

        let (rhs_cells, rhs_tail) = rhs_cells.split_at(self.limbs_count_limit.get());

        if rhs_tail.iter().any(|cell| {
            bool::from(cell.value().unwrap().copied().unwrap_or_default().is_zero()).not()
        }) {
            return Err(big_uint::Error::LimbLimitReached {
                limit: self.limbs_count_limit,
                actual: rhs_cells.len() + rhs_tail.len(),
            }
            .into());
        }

        Ok(SumContext {
            rhs: rhs_cells.to_vec(),
            res: OverflowingBigUint {
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

        let mult_selector = &self.config().q_m[0];
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
            res: OverflowingBigUint {
                cells: production_cells,
                max_word: min_limbs_count * rhs_max_word * lhs_max_word,
            },
        })
    }

    /// Re-group limbs of `BigUint`
    ///
    /// This function performs re-grouping limbs
    /// With [`calc_limbs_per_group`] we calculate how many
    /// limbs will fit in one group, given that the current
    /// limbs are merged into new limbs. The result is wrapped
    /// in [`GroupedBigUint`]
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
        bignat_cells: OverflowingBigUint<F>,
    ) -> Result<GroupedBigUint<F>, Error> {
        trace!("Group {} limbs: {:?}", bignat_cells.len(), bignat_cells);

        let carry_bits =
            calc_carry_bits(&big_uint::f_to_nat(&bignat_cells.max_word), self.limb_width)?;
        let limbs_per_group = calc_limbs_per_group::<F>(carry_bits, self.limb_width)?.get();

        let group_count = bignat_cells.cells.len().sub(1).div(limbs_per_group).add(1);

        debug!(
            "group {bignat_cells:?}:
            limbs_count: {}
            limb_width: {limb_width},
            carry_bits: {carry_bits:?},
            limbs_per_group: {limbs_per_group},
            group_count: {group_count}",
            bignat_cells.cells.len(),
            limb_width = self.limb_width.get()
        );

        let bignat_limb_column = &self.config().state[0];
        let bignat_limb_shift = &self.config().q_1[0];
        let current_group_value_column = &self.config().state[1];
        let current_group_selector = &self.config().q_1[1];

        let group_output_value_column = &self.config().out;
        let group_output_selector = &self.config().q_o;

        let limb_block = iter::successors(Some(F::ONE), |l| Some(l.double()))
            .nth(self.limb_width.get())
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

        let grouped_max_word: BigUintRaw =
            (0..limbs_per_group).fold(BigUintRaw::zero(), |mut acc, i| {
                acc.set_bit((i * self.limb_width.get()) as u64, true);
                acc
            });

        Ok(GroupedBigUint {
            cells: grouped,
            max_word: big_uint::nat_to_f::<F>(&grouped_max_word).unwrap() * bignat_cells.max_word,
        })
    }

    /// Compares two [`GroupedBigUint`] numbers for equality.
    ///
    /// The algorithm can be described as follows:
    /// ```latex
    /// Given:
    /// lhs = \sum_i lhs_i w^i, where lhs_i < w_M
    /// rhs = \sum_i rhs_i w^i, where rhs_i < w_M
    /// m = \sum_i w_M w^i = \sum_i m_i w^i, where m_i < w
    ///
    /// We form the equation:
    /// x + m - y = \sum_i (lhs_i + w_M - rhs_i) w^i \stackrel{?}{=} \sum_i m_i w^i
    /// ```
    ///
    /// This method checks the equality of two big numbers by leveraging the concept of carry.
    /// The comparison is done by considering the maximum word size `w_M`.
    ///
    /// Parameters:
    /// - `lhs` & `rhs`: The two bignat numbers, represented in limbs, that we are comparing.
    /// - `m`: A special number where each limb is `max_word` (`w_M`).
    /// - `w_M`: The maximum word size, which depends on the operations previously done on the numbers.
    ///          It accounts for any overflow relative to `self.limb_width`.
    ///
    /// # Arithmetization
    ///
    /// ```markdown
    /// |----------|-------|----------|-------|----------|-------|----------|-------|-----------|-------------|-------|-------------|
    /// | state[0] | q_1[0]| state[1] | q_1[1]| state[2] | q_1[2]| state[3] | q_1[3]|   input   |    q_i      |  out  |     q_o     |
    /// |----------|-------|----------|-------|----------|-------|----------|-------|-----------|-------------|-------|-------------|
    /// |   ...    |  ...  |   ...    |  ...  |   ...    |  ...  |   ...    |  ...  |   ...     |    ...      |  ...  |     ...     |
    /// |  lhs[k]  |   1   |  rhs[k]  |  -1   |   m_k    |  -1   | max_word |   1   | carry[k-1]|     1       | carry | -target_base|
    /// |   ...    |  ...  |   ...    |  ...  |   ...    |  ...  |   ...    |  ...  |   ...     |    ...      |  ...  |     ...     |
    /// |----------|-------|----------|-------|----------|-------|----------|-------|-----------|-------------|-------|-------------|
    /// ```
    ///
    /// We express the expression above through main_gate:
    /// `lhs[k] - rhs[k] - m_i + max_ord + carry[k-1] - carry[k] * target_base`
    /// `state[0] - state[1] + state[3] + state[4] + prev_carry - carry * target_base`
    ///
    /// - `target_base` - is the maximum word for the original limb length plus one (`1 << limb_width`)
    /// - `m_i` is calculated according to the following rules:
    /// ```no_compile
    /// let mut accumulated_extra = 0;
    /// let target_base = 1 << limb_width;
    /// let mut m = vec![];
    /// for i in 0..n {
    ///     accumulated_extra += &max_word_bn;
    ///     m[i] = accumulated_extra % &target_base_bn;
    ///     accumulated_extra /= &target_base_bn;
    /// }
    /// ```
    /// - also at each step except the last one we check that the carry
    ///   fits ([`BigUintMulModChip::check_fits_in_bits`]) into the carry
    ///   bits ([`calc_carry_bits`]).
    /// - in the last step, we check that `carry[n] = m[n]`
    fn is_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: GroupedBigUint<F>,
        rhs: GroupedBigUint<F>,
    ) -> Result<(), Error> {
        let limb_width = self.limb_width.get();

        let max_word_bn: BigUintRaw = cmp::max(
            big_uint::f_to_nat(&lhs.max_word),
            big_uint::f_to_nat(&rhs.max_word),
        );
        let max_word: F = big_uint::nat_to_f(&max_word_bn).unwrap();

        debug!("max word: {max_word_bn}");

        let target_base_bn = BigUintRaw::one() << limb_width;
        let target_base: F = big_uint::nat_to_f(&target_base_bn).expect("TODO");

        let mut accumulated_extra = BigUintRaw::zero();
        let carry_bits_len = calc_carry_bits(&max_word_bn, self.limb_width)?;
        debug!("carry_bits {carry_bits_len}");

        let lhs_column = &self.config().state[0];
        let lhs_selector = &self.config().q_1[0];

        let rhs_column = &self.config().state[1];
        let rhs_selector = &self.config().q_1[1];

        let m_i_column = &self.config().state[2];
        let m_i_selector = &self.config().q_1[2];

        let max_word_column = &self.config().state[3];
        let max_word_selector = &self.config().q_1[3];

        let prev_carry_column = &self.config().input;
        let prev_carry_coeff = &self.config().q_i;
        let mut prev_carry_cell = None;

        let carry_column = &self.config().out;
        let carry_coeff = &self.config().q_o;

        let max_cells_len = cmp::max(lhs.cells.len(), rhs.cells.len());

        // TODO Add check about last carry cell
        lhs.cells
            .into_iter()
            .zip_longest(rhs.cells.into_iter())
            .enumerate()
            .map(|(limb_index, cells)| -> Result<(), Error> {
                debug!("for limb_index {limb_index} & row offset: {}", ctx.offset);

                ctx.assign_fixed(
                    || format!("selector lhs {limb_index}"),
                    *lhs_selector,
                    F::ONE,
                )?;

                ctx.assign_fixed(
                    || format!("selector rhs {limb_index}"),
                    *rhs_selector,
                    -F::ONE,
                )?;

                // m_i
                accumulated_extra += &max_word_bn;

                let assigned_m_i = ctx.assign_advice(
                    || "max word for equal check",
                    *m_i_column,
                    Value::known(
                        big_uint::nat_to_f(&(&accumulated_extra % &target_base_bn)).expect("TODO"),
                    ),
                )?;
                debug!("assigned_m_i: {:?}", assigned_m_i);

                accumulated_extra /= &target_base_bn;

                ctx.assign_fixed(
                    || format!("selector m_i {limb_index}"),
                    *m_i_selector,
                    -F::ONE,
                )?;

                // max_word ($W_m$)
                let assigned_max_word = ctx.assign_advice(
                    || "max word for equal check",
                    *max_word_column,
                    Value::known(max_word),
                )?;
                ctx.assign_fixed(
                    || format!("selector rhs {limb_index}"),
                    *max_word_selector,
                    F::ONE,
                )?;

                debug!("max word: {:?}", assigned_max_word);

                ctx.assign_fixed(
                    || format!("carry[{limb_index}-1] coeff"),
                    *prev_carry_coeff,
                    F::ONE,
                )?;

                // carry[i-1]
                let prev_carry = if let Some(prev_carry_cell) = &prev_carry_cell {
                    debug!("Take prev carry: {:?}", prev_carry_cell);

                    ctx.assign_advice_from(
                        || format!("carry_{limb_index}-1"),
                        *prev_carry_column,
                        prev_carry_cell,
                    )?
                    .value()
                    .copied()
                } else {
                    Value::known(F::ZERO)
                };

                let lhs_sub_rhs = match cells {
                    EitherOrBoth::Both(lhs, rhs) => {
                        // lhs
                        let lhs_limb = ctx.assign_advice_from(
                            || format!("lhs {limb_index} for calc dividend"),
                            *lhs_column,
                            &lhs,
                        )?;

                        // -rhs
                        let rhs_limb = ctx.assign_advice_from(
                            || format!("rhs {limb_index} for calc dividend"),
                            *rhs_column,
                            &rhs,
                        )?;

                        lhs_limb.value().map(|f| *f) - rhs_limb.value()
                    }
                    EitherOrBoth::Left(lhs) => ctx
                        .assign_advice_from(
                            || format!("lhs {limb_index} for calc dividend"),
                            *lhs_column,
                            &lhs,
                        )?
                        .value()
                        .map(|f| *f),
                    EitherOrBoth::Right(rhs) => ctx
                        .assign_advice_from(
                            || format!("rhs {limb_index} for check zero"),
                            *rhs_column,
                            &rhs,
                        )?
                        .value()
                        .map(|v| -(*v)),
                };

                ctx.assign_fixed(
                    || format!("carry_{limb_index} coeff"),
                    *carry_coeff,
                    -target_base,
                )?;
                // -carry [i] * w
                let carry =
                    (prev_carry + lhs_sub_rhs + assigned_max_word.value()).map(|dividend_carry| {
                        let dividend_carry = big_uint::f_to_nat(&dividend_carry);

                        big_uint::nat_to_f(&(dividend_carry / &target_base_bn)).unwrap()
                    });

                let carry_cell =
                    ctx.assign_advice(|| format!("carry_{limb_index}"), *carry_column, carry)?;

                if limb_index != max_cells_len - 1 {
                    prev_carry_cell = Some({
                        ctx.next();
                        self.decompose_in_bits(ctx, carry_cell.clone(), carry_bits_len)?;

                        carry_cell
                    });
                } else {
                    prev_carry_cell = Some(carry_cell);
                };

                ctx.next();

                Ok(())
            })
            .collect::<Result<Vec<()>, _>>()?;

        ctx.assign_fixed(|| "last carry coeff", *carry_coeff, F::ONE)?;
        // -carry [i]
        let _last_carry = ctx.assign_advice_from(
            || "last carry",
            *carry_column,
            prev_carry_cell.expect("Always assigned, because limbs not empty"),
        )?;
        let _m_n = ctx.assign_advice(
            || "`m_n` for equal check",
            *m_i_column,
            Value::known(big_uint::nat_to_f(&accumulated_extra).unwrap()),
        )?;
        ctx.assign_fixed(|| "selector `m_n`", *m_i_selector, -F::ONE)?;

        ctx.next();

        Ok(())
    }

    /// From slice bytes, creates bit cells and verifies that they are indeed bits.
    /// Takes the first `expected_bits_count`.
    ///
    /// For every `k` rows looks like:
    /// ```markdown
    /// |   ---   |   ---   |  ---     |   ---    |  ---  |
    /// |  input  |   q_i   | state[0] | state[1] |  q_m  |
    /// |   ---   |   ---   |   ---    |   ---    |  ---  |
    /// |   ...   |   ...   |   ...    |   ...    |  ...  |
    /// |   b_i   |    1    |   b_i    |   b_i    |  -1   |
    /// |   ...   |   ...   |   ...    |   ...    |  ...  |
    /// ```
    /// Because:
    /// `input * q_i * q_m * q1[1] * q2[1] == 0` =>
    /// `b_i - b_i * b_i == 0`
    /// it's corrected only for `1` or `0`
    ///
    /// Bits represented in LE
    /// Return cells with bits
    fn assign_and_check_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        buffer: &[u8],
        expected_bits_count: NonZeroUsize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let bit_column = self.config().input;
        let bit_selector = self.config().q_i;

        let bit_square_multipliers_columns = self.config().state;
        let square_multipliers_coeff = self.config().q_m[0];

        // TODO Check BigEngian || LittleEndian
        let mut bits_repr = LittleEndianReader::new(buffer);
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

    /// Checks that the cell value fits within the given number of bits
    ///
    /// First it splits the cell value into bits, takes the first
    /// `expected_bits_count` and assigns them to advice column,
    /// proving that each of the bits is 0 or 1 by
    /// [`BigUintMulModChip::assign_and_check_bits`].
    ///
    /// Second, it checks that the sum of all these bits converges
    /// to the cell value using multiplication by powers of two.
    /// Proof will fail if the cell value takes up more bits than
    /// expected.
    ///
    /// For every `k` rows looks like:
    /// ```markdown
    /// |----------|---------|----------|---------|------------|-------|---------|-------|
    /// | state[0] |  q1[0]  | state[1] |  q1[0]  |   input    |  q_i  | output  |  q_o  |
    /// |----------|---------|----------|---------|------------|-------|---------|-------|
    /// |   ...    |   ...   |   ...    |   ...   |    ...     |  ...  |   ...   |  ...  |
    /// |   b_k    |   2^k   |  b_{k+1} | 2^{k+1} | chunk_{l-1}|   1   | chunk_l |  -1   |
    /// |   ...    |   ...   |   ...    |   ...   |    ...     |  ...  |   ...   |  ...  |
    /// |----------|---------|----------|---------|------------|-------|---------|-------|
    /// ```
    ///
    /// At the end, a constraint is made that the incoming cell is equal to the new counted cell.
    pub fn decompose_in_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        cell: AssignedCell<F, F>,
        expected_bits_count: NonZeroUsize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let value_repr = cell
            .value()
            .map(|v| v.to_repr())
            .unwrap()
            .unwrap_or_else(|| F::ZERO.to_repr());

        // proof here all bits in [0, 1]
        let bits_cells =
            self.assign_and_check_bits(ctx, value_repr.as_ref(), expected_bits_count)?;

        let prev_chunk_sum_col = self.config().input;
        let prev_chunk_sum_selector = self.config().q_i;

        let out_chunk_sum_col = self.config().out;
        let out_chunk_sum_selector = self.config().q_o;

        let bits_with_coeff =
            itertools::multizip((0.., bits_cells.iter(), util::get_power_of_two_iter::<F>()));

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

                ctx.assign_fixed(|| "chunk_sum_coeff", out_chunk_sum_selector, -F::ONE)
                    ?;

                let output = ctx.assign_advice(|| "chunk_sum", out_chunk_sum_col, current_chunk_sum)
                    ?;

                ctx.next();

                Result::<_, Error>::Ok(Some(output))
            })?
            .expect("Safe, because carry_bits != 0");

        ctx.constrain_equal(final_sum_cell.cell(), cell.cell())?;

        Ok(bits_cells)
    }
}

#[derive(Debug, Clone)]
pub struct OverflowingBigUint<F: ff::PrimeField> {
    pub cells: Vec<AssignedCell<F, F>>,
    pub max_word: F,
}

impl<F: ff::PrimeField> OverflowingBigUint<F> {
    pub fn new(cells: Vec<AssignedCell<F, F>>, limb_width: NonZeroUsize) -> Self {
        let max_word_without_overflow: F =
            big_uint::nat_to_f(&big_uint::get_big_int_with_n_ones(limb_width.get()))
                .unwrap_or_default();

        Self {
            cells,
            max_word: max_word_without_overflow,
        }
    }
}

impl<F: ff::PrimeField> Deref for OverflowingBigUint<F> {
    type Target = [AssignedCell<F, F>];
    fn deref(&self) -> &Self::Target {
        self.cells.as_slice()
    }
}

#[derive(Debug, Clone)]
struct GroupedBigUint<F: ff::PrimeField> {
    cells: Vec<AssignedCell<F, F>>,
    max_word: F,
}
impl<F: ff::PrimeField> Deref for GroupedBigUint<F> {
    type Target = [AssignedCell<F, F>];
    fn deref(&self) -> &Self::Target {
        self.cells.as_slice()
    }
}

#[derive(Debug)]
pub struct ModOperationResult<F: PrimeField> {
    pub quotient: Vec<AssignedCell<F, F>>,
    pub remainder: Vec<AssignedCell<F, F>>,
}

impl<F: PrimeField> Deref for ModOperationResult<F> {
    type Target = [AssignedCell<F, F>];
    fn deref(&self) -> &Self::Target {
        self.remainder.as_slice()
    }
}

#[derive(Debug)]
pub struct MultContext<F: PrimeField> {
    lhs: Vec<AssignedCell<F, F>>,
    rhs: Vec<AssignedCell<F, F>>,
    res: OverflowingBigUint<F>,
}

pub struct SumContext<F: PrimeField> {
    pub rhs: Vec<AssignedCell<F, F>>,
    pub res: OverflowingBigUint<F>,
}

impl<F: ff::PrimeField> BigUintMulModChip<F> {
    /// Converts a single assigned cell to a list of limbs, according to the limb width and count limit.
    ///
    /// This function assigns to the region context, evaluated `AssignedCells` representing the limbs of the
    /// original `AssignedCell` in the `BigUint` representation.
    ///
    /// # Arguments
    /// * `ctx`: Mutable reference to the `RegionCtx` provides the constraint system and metadata.
    /// * `input`: A reference to the `AssignedCell` representing the input value.
    ///
    /// For every `k` rows looks like:
    /// ```markdown
    /// |   ---    |  ---  |  ---  |  ---  |  ---  |  ---   |
    /// | state[0] | q1[0] |  q_i  | input |  q_o  | output |
    /// |   ---    |  ---  |  ---  |  ---  |  ---  |  ---   |
    /// |   ...    |  ...  |  ...  |  ...  |  ...  |  ...   |
    /// |  limb_k  |   1   | shift |  p_k  |  -1   |  s_k   |
    /// |   ...    |  ...  |  ...  |  ...  |  ...  |  ...   |
    /// ```
    /// where:
    ///     - `limb_k` it's limb of input in big uint representation
    ///     - `shift` it's constant equal `2 ^ self.limb_width`
    ///     - `p_k` partial sum of [0..k-1] limbs
    ///     - `s_k` partial sum of [0..k] limbs
    ///
    /// The `s_n` it's equal with original input and check by copy constraint
    pub fn from_assigned_cell_to_limbs(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        input: &AssignedCell<F, F>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        debug!("Input: {:?}", input.value().unwrap());
        let bignat_limb_column = &self.config().state[0];
        let bignat_limb_shift = &self.config().q_1[0];

        let prev_column = &self.config().input;
        let prev_selector = &self.config().q_i;

        let partial_sum_column = &self.config().out;
        let partial_sum_selector = &self.config().q_o;

        let shift = F::from(2).pow_vartime([self.limb_width.get() as u64]); // base = 2^limb_width
        debug!("Shift {shift:?}");

        let mut prev_partial_sum = Option::<AssignedCell<F, F>>::None;

        let mut limbs = BigUint::from_f(
            &input.value().unwrap().copied().unwrap_or_default(),
            self.limb_width,
            self.limbs_count_limit,
        )?
        .limbs()
        .to_vec();

        limbs.resize(self.limbs_count_limit.get(), F::ZERO);

        let mut limbs = limbs
            .into_iter()
            .enumerate()
            .rev()
            .inspect(|(limb_index, limb)| trace!("limbs[{limb_index}]={limb:?}"))
            .map(|(limb_index, limb)| {
                debug!("Limb[{limb_index}] = {limb:?}");

                ctx.assign_fixed(
                    || format!("{limb_index} selector"),
                    *bignat_limb_shift,
                    F::ONE,
                )?;

                let limb_cell = ctx.assign_advice(
                    || format!("{limb_index} limb"),
                    *bignat_limb_column,
                    Value::known(limb),
                )?;

                let shift = ctx
                    .assign_fixed(
                        || {
                            format!(
                                "previous limbs (to {:?}) sum selector",
                                limb_index.checked_sub(1)
                            )
                        },
                        *prev_selector,
                        shift,
                    )?
                    .value()
                    .copied();

                let shifted_prev = shift
                    * match &prev_partial_sum {
                        Some(prev_partial_sum) => ctx
                            .assign_advice_from(
                                || {
                                    format!(
                                        "previous limbs (to {:?}) sum value",
                                        limb_index.checked_sub(1)
                                    )
                                },
                                *prev_column,
                                prev_partial_sum,
                            )?
                            .value()
                            .copied(),
                        _ => Value::known(F::ZERO),
                    };

                debug!(
                    "Previos partial sum: {:?}",
                    prev_partial_sum.as_ref().and_then(|c| *c.value().unwrap())
                );
                debug!("Previos shifted partial sum: {:?}", shifted_prev.unwrap());

                ctx.assign_fixed(
                    || format!("sum of limbs from 0 to {limb_index} selector",),
                    *partial_sum_selector,
                    -F::ONE,
                )?;

                prev_partial_sum = Some(ctx.assign_advice(
                    || format!("sum of limbs from 0 to {limb_index}",),
                    *partial_sum_column,
                    shifted_prev + limb_cell.value(),
                )?);

                debug!(
                    "New partial sum: {:?}",
                    prev_partial_sum.as_ref().unwrap().value().unwrap()
                );

                ctx.next();

                Result::<_, Error>::Ok(limb_cell)
            })
            .collect::<Result<Vec<_>, _>>()?;

        assert_eq!(
            prev_partial_sum.clone().unwrap().value().unwrap(),
            input.value().unwrap()
        );
        ctx.constrain_equal(prev_partial_sum.unwrap().cell(), input.cell())?;

        limbs.reverse();
        Ok(limbs)
    }

    /// Performs the multiplication of `lhs` and `rhs` taking into account the `modulus`.
    ///
    /// This method serves as an implementation of modular multiplication in the context
    /// of Halo2 protocol. This implementation leverages the use of the `BigUintMulModChip`
    /// to perform efficient calculation of large primes.
    ///
    /// # Arguments
    /// * `ctx`: mutable reference to the `RegionCtx` which provides the constraint system and metadata.
    /// * `lhs`: array of `AssignedCell` representing the left hand side of the operation.
    /// * `rhs`: array of `AssignedCell` representing the right hand side of the operation.
    /// * `modulus`: array of `AssignedCell` representing the modulus.
    ///
    /// # Order of Operations
    /// 1. Convert `lhs`, `rhs`, and `modulus` to `BigUint` objects using [`big_uint::BigUint::from_assigned_cells`].
    /// 2. Perform the modular multiplication `lhs * rhs` using the converted `BigUint` numbers.
    /// 2.1. This includes the calculation of the quotient and remainder.
    /// 3. Assign the modular multiplication to the left using [`Self::assign_mult`].
    /// 4. Calculate `q * m` and the sum `q * m + r` using [`Self::assign_mult`] and [`Self::assign_sum`] respectively.
    /// 5. Group the limbs of left and right operations using [`Self::group_limbs`].
    /// 6. Check for the equivalence between the left and right operations using [`Self::is_equal`].
    ///
    /// # Returns
    /// * A result wrapping [`MultModResult`] object containing the calculated quotient and remainder.
    ///
    /// # Errors
    /// This method will return an error if there is an issue in the conversion of `lhs`, `rhs`, or `modulus` into `BigUint`
    /// or if the assignment of multiplication and addition fails
    pub fn mult_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &[AssignedCell<F, F>],
        rhs: &[AssignedCell<F, F>],
        modulus: &[AssignedCell<F, F>],
    ) -> Result<ModOperationResult<F>, Error> {
        // lhs * rhs = q * m + r

        let to_bn = |val| {
            big_uint::BigUint::from_assigned_cells(val, self.limb_width, self.limbs_count_limit)
        };

        let mod_bn = to_bn(modulus)?;

        let lhs_bi = to_bn(lhs)?.map(|bn| bn.into_bigint());
        let rhs_bi = to_bn(rhs)?.map(|bn| bn.into_bigint());
        let mod_bi = mod_bn.as_ref().map(|bn| bn.into_bigint());

        let (q, r) = lhs_bi
            .as_ref()
            .zip(rhs_bi.as_ref())
            .zip(mod_bi.as_ref())
            .map(|((lhs_bi, rhs_bi), mod_bi)| {
                let prod = lhs_bi * rhs_bi;
                Result::<_, Error>::Ok((
                    self.to_bignat(&(&prod / mod_bi))?,
                    self.to_bignat(&(&prod % mod_bi))?,
                ))
            })
            .transpose()?
            .unzip();

        // lhs * rhs
        let max_word_without_overflow: F =
            big_uint::nat_to_f(&big_uint::get_big_int_with_n_ones(self.limb_width.get()))
                .unwrap_or_default();

        let MultContext { res: left, .. } = self.assign_mult(
            ctx,
            lhs,
            rhs,
            &max_word_without_overflow,
            &max_word_without_overflow,
        )?;

        let empty = iter::repeat(F::ZERO)
            .take(self.limbs_count_limit.get())
            .collect::<Box<[_]>>();

        // q * m + r
        let MultContext {
            lhs: assigned_q,
            res: q_mul_m,
            ..
        } = self.assign_mult(
            ctx,
            q.as_ref().map(|bn| bn.limbs()).unwrap_or(&empty),
            mod_bn.as_ref().map(|bn| bn.limbs()).unwrap_or(&empty),
            &max_word_without_overflow,
            &max_word_without_overflow,
        )?;
        let SumContext {
            rhs: assigned_r,
            res: right,
        } = self.assign_sum(
            ctx,
            &q_mul_m,
            r.as_ref().map(|bn| bn.limbs()).unwrap_or(&empty),
        )?;

        // q * m + r
        let grouped_left = self.group_limbs(ctx, left)?;
        let grouped_right = self.group_limbs(ctx, right)?;

        self.is_equal(ctx, grouped_left, grouped_right)?;

        Ok(ModOperationResult {
            quotient: assigned_q,
            remainder: assigned_r,
        })
    }

    /// Performs modular reduction of `val` by `modulus`.
    ///
    /// This method is part of the Halo2 protocol's arithmetic operations on big integers.
    /// It reduces a big integer value (`val`) modulo a given modulus (`modulus`) efficiently
    /// using the `BigUintMulModChip`. The operation is crucial in cryptographic computations
    /// where maintaining values within a finite field is necessary.
    ///
    /// # Arguments
    /// * `ctx`: mutable reference to the `RegionCtx` which provides the constraint system
    ///   and metadata necessary for the operation within the Halo2 protocol.
    /// * `val`: array of `AssignedCell` representing the value to be reduced.
    /// * `modulus`: array of `AssignedCell` representing the modulus for the reduction.
    ///
    /// # Order of Operations
    /// 1. Convert `val` and `modulus` to `BigUint` objects using
    ///    [`big_uint::BigUint::from_assigned_cells`].
    /// 2. Perform the modular reduction `val % modulus` using the converted `BigUint` numbers.
    /// 2.1. This includes the calculation of the quotient and remainder.
    /// 3. Assign the reduction result using [`Self::assign_mult`] for `q * m` (quotient times modulus)
    ///    and [`Self::assign_sum`] for `q * m + r` (sum of quotient times modulus and remainder).
    /// 4. Group the limbs of the calculated values using [`Self::group_limbs`].
    /// 5. Check for equivalence between the original value and the calculated sum using
    ///    [`Self::is_equal`].
    ///
    /// # Returns
    /// * A result wrapping [`ModOperationResult`] object containing the calculated quotient
    ///   and remainder from the modular reduction.
    ///
    /// # Errors
    /// This method will return an error if there is an issue in the conversion of `val` or
    /// `modulus` into `BigUint`, or if the assignment of multiplication and addition fails.
    pub fn red_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        val: OverflowingBigUint<F>,
        modulus: &[AssignedCell<F, F>],
    ) -> Result<ModOperationResult<F>, Error> {
        // lhs * rhs = q * m + r

        let to_bn = |val| {
            big_uint::BigUint::from_assigned_cells(val, self.limb_width, self.limbs_count_limit)
        };

        let mod_bn = to_bn(modulus)?;
        debug!("red_mod: mod {mod_bn:?}");

        let val_bi = to_bn(&val.cells)?.map(|bn| bn.into_bigint());
        debug!("red_mod: val {val_bi:?}");
        let mod_bi = mod_bn.as_ref().map(|bn| bn.into_bigint());
        debug!("red_mod: mod_bi {mod_bi:?}");

        let (q, r) = val_bi
            .as_ref()
            .zip(mod_bi.as_ref())
            .map(|(val_bi, mod_bi)| {
                Result::<_, Error>::Ok((
                    self.to_bignat(&(val_bi / mod_bi))?,
                    self.to_bignat(&(val_bi % mod_bi))?,
                ))
            })
            .transpose()?
            .unzip();

        debug!(
            "
            red_mod: {q:?} * {mod_bi:?} + {r:?} = {val_bi:?} mod {mod_bi:?}
        "
        );

        // lhs * rhs

        let empty = iter::repeat(F::ZERO)
            .take(self.limbs_count_limit.get())
            .collect::<Box<[_]>>();

        // q * m + r
        let MultContext {
            lhs: assigned_q,
            res: q_mul_m,
            ..
        } = self.assign_mult(
            ctx,
            q.as_ref().map(|bn| bn.limbs()).unwrap_or(&empty),
            mod_bn.as_ref().map(|bn| bn.limbs()).unwrap_or(&empty),
            &val.max_word,
            &val.max_word,
        )?;
        let SumContext {
            rhs: assigned_r,
            res: right,
        } = self.assign_sum(
            ctx,
            &q_mul_m,
            r.as_ref().map(|bn| bn.limbs()).unwrap_or(&empty),
        )?;

        // q * m + r
        let left = OverflowingBigUint {
            cells: val.to_vec(),
            max_word: val.max_word,
        };

        let grouped_left = self.group_limbs(ctx, left)?;
        let grouped_right = self.group_limbs(ctx, right)?;

        self.is_equal(ctx, grouped_left, grouped_right)?;

        Ok(ModOperationResult {
            quotient: assigned_q,
            remainder: assigned_r,
        })
    }
}

impl<F: ff::PrimeFieldBits> BigUintMulModChip<F> {
    /// Converts a big uint number in assigned limbs form to bits, where each limb occupies transmitted bits.
    ///
    /// Use [`MainGate::le_num_to_bits`] per each limb and concat all results
    pub fn to_le_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        limbs: &[AssignedCell<F, F>],
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        limbs.iter().try_fold(
            Vec::with_capacity(limbs.len() * self.limb_width.get()),
            |mut bits, limb| {
                bits.extend(
                    self.main_gate
                        .le_num_to_bits(ctx, limb.clone(), self.limb_width)?,
                );
                Ok(bits)
            },
        )
    }
}

impl<F: ff::PrimeField> Chip<F> for BigUintMulModChip<F> {
    type Config = MainGateConfig<MAIN_GATE_T>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        self.main_gate.config()
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

fn calc_carry_bits(max_word: &BigUintRaw, limb_width: NonZeroUsize) -> Result<NonZeroUsize, Error> {
    // FIXME: Is `f64` really needed here
    // We can calculate `log2` for BigUintRaw without f64
    let carry_bits = max_word
        .mul(BigUintRaw::one() + BigUintRaw::one())
        .to_f64()
        .ok_or(Error::CarryBitsCalculate)?
        .log2()
        .sub(limb_width.get() as f64)
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
    limb_width: NonZeroUsize,
) -> Result<NonZeroUsize, Error> {
    let capacity = F::CAPACITY as usize;
    NonZeroUsize::new(
        capacity
            .checked_sub(carry_bits.get())
            .ok_or(Error::CarryBitsEqualCapacity)?
            .checked_div(limb_width.get())
            .expect("Unreachable, because limb_width != 0"),
    )
    .ok_or(Error::ZeroLimbsPerGroup)
}

#[cfg(test)]
mod tests;
