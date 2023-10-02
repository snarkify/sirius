use crate::polynomial::sparse::SparseMatrix;
use ff::PrimeField;
use halo2_proofs::plonk::{Any, Column};
use std::collections::HashSet;

// Helper function to convert cell indices (column, row) to index in Z vector
pub(crate) fn cell_to_z_idx(column: usize, row: usize, num_rows: usize, num_io: usize) -> usize {
    match column {
        // instance column
        column if column < 1 => row + column * num_rows, // instance column
        // advice columns
        column => num_io + (column - 1) * num_rows + row,
    }
}

pub(crate) fn column_index(idx: usize, columns: &[Column<Any>]) -> usize {
    let column = columns[idx];
    let offset = match column.column_type() {
        Any::Instance => 0,
        Any::Advice(_) => 1,
        Any::Fixed => panic!("fixed column is not allowed"),
    };
    column.index() + offset
}

pub(crate) fn fill_sparse_matrix<F: PrimeField>(
    sparse_matrix_p: &mut SparseMatrix<F>,
    num_advice: usize,
    num_rows: usize,
    num_io: usize,
    columns: &[Column<Any>],
) {
    let num_columns = num_advice + 1; // 1 is the number of instance column
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
