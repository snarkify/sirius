use crate::plonk::permutation::Assembly;
use crate::polynomial::sparse::SparseMatrix;
use crate::polynomial::Expression;
use ff::PrimeField;
use halo2_proofs::plonk::{Any, Column};
use halo2_proofs::plonk::{ConstraintSystem, Expression as PE};
use std::collections::HashSet;

// Helper function to convert cell indices (column, row) to index in Z vector
pub(crate) fn cell_to_z_idx(column: usize, row: usize, num_rows: usize, num_io: usize) -> usize {
    if num_io > 0 && column >= 1 {
        num_io + (column - 1) * num_rows + row
    } else {
        row + column * num_rows
    }
}

/// return the index of instance column from columns
pub(crate) fn instance_column_index(columns: &[Column<Any>]) -> Option<usize> {
    columns
        .iter()
        .position(|&column| *column.column_type() == Any::Instance)
}

pub fn column_index(idx: usize, columns: &[Column<Any>]) -> usize {
    let column = columns[idx];
    let offset = match column.column_type() {
        Any::Instance => 0,
        Any::Advice(_) => 1,
        Any::Fixed => panic!(
            "fixed column is not allowed in the copy constraint, it will break during folding"
        ),
    };
    if instance_column_index(columns).is_some() {
        column.index() + offset
    } else {
        column.index()
    }
}

pub(crate) fn fill_sparse_matrix<F: PrimeField>(
    sparse_matrix_p: &mut SparseMatrix<F>,
    num_advice: usize,
    num_rows: usize,
    num_io: usize,
    columns: &[Column<Any>],
) {
    let num_columns = if num_io > 0 {
        num_advice + 1
    } else {
        num_advice
    }; // 1 is the number of instance column
    let all_columns: HashSet<usize> = (0..num_columns).collect();
    let set_a: HashSet<usize> = columns
        .iter()
        .enumerate()
        .map(|(i, _)| column_index(i, columns))
        .collect();
    let columns_to_fill: HashSet<usize> = all_columns.difference(&set_a).cloned().collect();
    for col in columns_to_fill.iter() {
        for row in 0..num_rows {
            let z_idx = cell_to_z_idx(*col, row, num_rows, num_io);
            sparse_matrix_p.push((z_idx, z_idx, F::ONE));
        }
    }
}

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
        exprs[0].clone()
    }
}

/// construct sparse matrix P (size N*N) from copy constraints
/// since folding will change values of advice/instance column while keep fixed column values
/// we don't allow fixed column to be in the copy constraint here
/// suppose we have 1 instance column, n advice columns
/// and there are total of r rows. notice the instance column only contains `num_io = io` items
/// N = num_io + r*n. Let (i_1,...,i_{io}) be all values of the instance columns
/// and (x_1,...,x_{n*r}) be concatenate of advice columns.
/// define vector Z = (i_1,...,i_{io}, x_1,...,x_{n*r})
/// This function is to find the permutation matrix P such that the copy constraints are
/// equivalent to P * Z - Z = 0. This is invariant relation under our folding scheme
pub(crate) fn permutation_matrix<F: PrimeField>(
    k: usize,
    num_io: usize,
    cs: &ConstraintSystem<F>,
    permutation: &Assembly,
) -> SparseMatrix<F> {
    let mut sparse_matrix_p = Vec::new();
    let num_advice = cs.num_advice_columns();
    let columns = &cs.permutation.columns;
    let instance_column_idx = instance_column_index(columns);
    let num_rows = 1 << k;

    for (left_col, vec) in permutation.mapping.iter().enumerate() {
        for (left_row, cycle) in vec.iter().enumerate() {
            // skip rows that beyond the num_io in instance column
            if let Some(idx) = instance_column_idx {
                if left_col == idx && left_row >= num_io {
                    continue;
                }
            }
            let left_col = column_index(left_col, columns);
            let right_col = column_index(cycle.0, columns);
            let left_z_idx = cell_to_z_idx(left_col, left_row, num_rows, num_io);
            let right_z_idx = cell_to_z_idx(right_col, cycle.1, num_rows, num_io);
            sparse_matrix_p.push((left_z_idx, right_z_idx, F::ONE));
        }
    }

    fill_sparse_matrix(&mut sparse_matrix_p, num_advice, num_rows, num_io, columns);
    sparse_matrix_p
}
