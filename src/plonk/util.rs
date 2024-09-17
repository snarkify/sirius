use std::{collections::HashSet, iter};

use halo2_proofs::plonk::{Any, Column, ConstraintSystem, Expression as PE};
use tracing::*;

use crate::{
    ff::PrimeField,
    plonk::permutation::Assembly,
    polynomial::{sparse::SparseMatrix, Expression},
};

/// compress a vector of halo2 expressions into one by random linear combine a challenge
pub(crate) fn compress_halo2_expression<F: PrimeField>(
    exprs: &[PE<F>],
    num_selectors: usize,
    num_fixed: usize,
    challenge_index: usize,
) -> Expression<F> {
    let y = Expression::Challenge(challenge_index);
    if exprs.len() > 1 {
        exprs
            .iter()
            .map(|expr| Expression::from_halo2_expr(expr, num_selectors, num_fixed))
            .fold(Expression::Constant(F::ZERO), |acc, expr| {
                Expression::Sum(
                    Box::new(expr),
                    Box::new(Expression::Product(Box::new(acc), Box::new(y.clone()))),
                )
            })
    } else {
        Expression::from_halo2_expr(&exprs[0], num_selectors, num_fixed)
    }
}

/// compress a vector of [`Expression`] into one by random linear combine a challenge
pub(crate) fn compress_expression<F: PrimeField>(
    exprs: &[Expression<F>],
    challenge_index: usize,
) -> Expression<F> {
    let y = Expression::Challenge(challenge_index);
    if exprs.len() > 1 {
        exprs
            .iter()
            .fold(Expression::Constant(F::ZERO), |acc, expr| {
                Expression::Sum(
                    Box::new(expr.clone()),
                    Box::new(Expression::Product(Box::new(acc), Box::new(y.clone()))),
                )
            })
    } else {
        exprs
            .first()
            .cloned()
            .unwrap_or(Expression::Constant(F::ZERO))
    }
}

/// Constructs a sparse permutation matrix `P` of size `N * N` from copy constraints.
///
/// The function accounts for the changes due to folding, which affects the values of advice/instance
/// columns while keeping fixed column values unchanged. Consequently, fixed columns are not allowed
/// in copy constraints.
///
/// Assume we have 1 instance column and `n` advice columns, with a total of `r` rows. Note that the
/// instance column contains only `num_io` items:
///
/// `N = num_io + r * n`
///
/// Let `(i_1, ..., i_{io})` represent the values of the instance column, and
/// `(x_1, ..., x_{n * r})` be the concatenated values of the advice columns. Define the vector:
///
/// `Z = (i_1, ..., i_{io}, x_1, ..., x_{n * r})`
///
/// The goal is to find a permutation matrix `P` such that the copy constraints satisfy:
///
/// `P * Z - Z = 0`
///
/// This relation remains invariant under the folding scheme.
#[instrument(name = "permutation", skip_all)]
pub(crate) fn construct_permutation_matrix<F: PrimeField>(
    k_table_size: usize,
    num_io: &[usize],
    cs: &ConstraintSystem<F>,
    permutation: &Assembly,
) -> SparseMatrix<F> {
    let perm_columns = &cs.permutation.columns;

    let num_rows = 1 << k_table_size;
    let num_advice = cs.num_advice_columns();

    // Lengths of each row of the matrix
    let rows_len = num_io
        .iter()
        .copied()
        .chain(iter::repeat(num_rows).take(num_advice))
        .collect::<Box<[_]>>();

    let to_flat_column_offset = |column: Column<Any>| -> usize {
        match column.column_type() {
            Any::Instance => column.index(),
            Any::Advice(_) => num_io.len() + column.index(),
            Any::Fixed => unreachable!("'fixed column' can't be a part of permutation"),
        }
    };

    let to_flat_index = |column: Column<Any>, row: usize| -> usize {
        rows_len
            .iter()
            .take(to_flat_column_offset(column))
            .sum::<usize>()
            + row
    };

    let flated_rows = rows_len.iter().sum();
    let mut columns_not_in_perm = HashSet::<usize>::from_iter(0..num_io.len() + num_advice);

    let mut sparse_matrix_p = Vec::with_capacity(flated_rows);
    for (left_col, mapping_vec) in permutation.mapping.iter().enumerate() {
        let left_col = perm_columns[left_col];
        columns_not_in_perm.remove(&to_flat_column_offset(left_col));

        let instance_rows_count = match left_col.column_type() {
            Any::Instance => num_io.get(left_col.index()),
            _ => None,
        };

        for (left_row, (cycle_col, cycle_row)) in mapping_vec.iter().enumerate() {
            if matches!(
                instance_rows_count,
                Some(count) if left_row >= *count
            ) {
                continue;
            }

            let right_col = perm_columns[*cycle_col];
            columns_not_in_perm.remove(&to_flat_column_offset(right_col));

            let left_z_idx = to_flat_index(left_col, left_row);
            let right_z_idx = to_flat_index(right_col, *cycle_row);

            sparse_matrix_p.push((left_z_idx, right_z_idx, F::ONE));
        }
    }

    columns_not_in_perm.into_iter().for_each(|column_offset| {
        let col_offset = rows_len.iter().take(column_offset).sum::<usize>();

        for row in 0..num_rows {
            let z_idx = col_offset + row;
            sparse_matrix_p.push((z_idx, z_idx, F::ONE));
        }
    });

    sparse_matrix_p
}
