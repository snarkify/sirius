//! Adapted from halo2/halo2_proofs/src/plonk/permutation/keygen.rs
use halo2_proofs::{
    halo2curves::ff::PrimeField,
    plonk::{permutation::Argument, Any, Column, Error},
};
use serde::{ser::SerializeStruct, Serialize, Serializer};
use tracing::*;

use super::util;
use crate::polynomial::sparse::SparseMatrix;

#[derive(Clone, PartialEq, Default, Eq, Debug)]
pub struct Assembly {
    /// Columns that participate on the copy permutation argument.
    columns: Vec<Column<Any>>,
    /// Mapping of the actual copies done.
    pub(crate) mapping: Vec<Vec<(usize, usize)>>,
    /// Some aux data used to swap positions directly when sorting.
    aux: Vec<Vec<(usize, usize)>>,
    /// More aux data
    sizes: Vec<Vec<usize>>,
}

impl Assembly {
    /// n is the number of rows in one column
    pub(crate) fn new(n: usize, p: &Argument) -> Self {
        // Initialize the copy vector to keep track of copy constraints in all
        // the permutation arguments.
        let mut columns = Vec::with_capacity(p.columns.len() * n);
        for i in 0..p.columns.len() {
            // Computes [(i, 0), (i, 1), ..., (i, n - 1)]
            columns.push((0..n).map(|j| (i, j)).collect());
        }

        // Before any equality constraints are applied, every cell in the permutation is
        // in a 1-cycle; therefore mapping and aux are identical, because every cell is
        // its own distinguished element.
        Assembly {
            columns: p.columns.clone(),
            mapping: columns.clone(),
            aux: columns,
            sizes: vec![vec![1usize; n]; p.columns.len()],
        }
    }

    pub(crate) fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        let left_column = self
            .columns
            .iter()
            .position(|c| c == &left_column)
            .ok_or(Error::ColumnNotInPermutation(left_column))?;
        let right_column = self
            .columns
            .iter()
            .position(|c| c == &right_column)
            .ok_or(Error::ColumnNotInPermutation(right_column))?;

        // Check bounds
        if left_row >= self.mapping[left_column].len()
            || right_row >= self.mapping[right_column].len()
        {
            error!("(left_column, left_row)=({left_column}, {left_row}), (right_column, right_row)=({right_column}, {right_row}). left_row or right_row in the copy contraint exceed maximum length");
            return Err(Error::BoundsFailure);
        }

        // See https://zcash.github.io/halo2/design/proving-system/permutation.html for a description of this algorithm.
        let mut left_cycle = self.aux[left_column][left_row];
        let mut right_cycle = self.aux[right_column][right_row];

        // If left and right are in the same cycle, do nothing.
        if left_cycle == right_cycle {
            return Ok(());
        }

        if self.sizes[left_cycle.0][left_cycle.1] < self.sizes[right_cycle.0][right_cycle.1] {
            std::mem::swap(&mut left_cycle, &mut right_cycle);
        }

        // Merge the right cycle into the left one.
        self.sizes[left_cycle.0][left_cycle.1] += self.sizes[right_cycle.0][right_cycle.1];
        let mut i = right_cycle;
        loop {
            self.aux[i.0][i.1] = left_cycle;
            i = self.mapping[i.0][i.1];
            if i == right_cycle {
                break;
            }
        }

        let tmp = self.mapping[left_column][left_row];
        self.mapping[left_column][left_row] = self.mapping[right_column][right_row];
        self.mapping[right_column][right_row] = tmp;

        Ok(())
    }
}

impl Serialize for Assembly {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Define the structure name and number of fields to serialize.
        let mut state = serializer.serialize_struct("Assembly", 4)?;

        #[derive(Serialize)]
        struct ColumnWrapper {
            index: usize,
            column_type: u16,
        }

        impl From<Column<Any>> for ColumnWrapper {
            fn from(value: Column<Any>) -> Self {
                Self {
                    index: value.index(),
                    column_type: match value.column_type() {
                        Any::Instance => 0,
                        Any::Fixed => 1,
                        Any::Advice(advice) => 2 + advice.phase() as u16,
                    },
                }
            }
        }

        state.serialize_field(
            "columns",
            &self
                .columns
                .iter()
                .cloned()
                .map(ColumnWrapper::from)
                .collect::<Box<[_]>>(),
        )?;
        state.serialize_field("mapping", &self.mapping)?;
        state.serialize_field("aux", &self.aux)?;
        state.serialize_field("sizes", &self.sizes)?;

        state.end()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct PermutataionData {
    pub perm_assembly: Assembly,
    pub columns: Box<[Column<Any>]>,
}

impl PermutataionData {
    pub fn matrix<F: PrimeField>(
        &self,
        k_table_size: usize,
        num_io: &[usize],
        num_advice_columns: usize,
    ) -> SparseMatrix<F> {
        util::construct_permutation_matrix(
            k_table_size,
            num_io,
            num_advice_columns,
            &self.columns,
            &self.perm_assembly,
        )
    }

    #[instrument(level = "debug", skip_all)]
    pub(crate) fn rm_copy_constraints(
        mut self,
        instance_columns_to_remove: impl Iterator<Item = usize>,
    ) -> Self {
        let instance_columns = self
            .columns
            .iter()
            .filter(|column| column.column_type().eq(&Any::Instance))
            .map(|column| column.index())
            .collect::<Box<[_]>>();

        let mut columns_to_remove_set = instance_columns_to_remove
            .filter(|index| instance_columns.binary_search(index).is_ok())
            .collect::<Box<[_]>>();

        columns_to_remove_set.sort();

        for (column_index, column) in self.columns.iter().enumerate() {
            if columns_to_remove_set.binary_search(&column.index()).is_ok() {
                debug!("completely clearing all permutations for column {column:?}");
                for (row_index, mapping_cell) in self.perm_assembly.mapping[column_index]
                    .iter_mut()
                    .enumerate()
                {
                    *mapping_cell = (column_index, row_index);
                }
            } else {
                let row_count = self.perm_assembly.mapping[column_index].len();

                for row_index in 0..row_count {
                    let (mut next_i, mut next_j) =
                        self.perm_assembly.mapping[column_index][row_index];

                    let start = (column_index, row_index);
                    while (next_i, next_j) != start
                        && columns_to_remove_set
                            .binary_search(&self.columns[next_i].index())
                            .is_ok()
                    {
                        (next_i, next_j) =
                            if (next_i, next_j) == self.perm_assembly.mapping[next_i][next_j] {
                                start
                            } else {
                                self.perm_assembly.mapping[next_i][next_j]
                            };
                    }

                    self.perm_assembly.mapping[column_index][row_index] = (next_i, next_j);
                }
            }
        }

        self
    }
}

impl Serialize for PermutataionData {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("Assembly", 4)?;

        #[derive(Serialize)]
        struct ColumnWrapper {
            index: usize,
            column_type: u16,
        }

        impl From<Column<Any>> for ColumnWrapper {
            fn from(value: Column<Any>) -> Self {
                Self {
                    index: value.index(),
                    column_type: match value.column_type() {
                        Any::Instance => 0,
                        Any::Fixed => 1,
                        Any::Advice(advice) => 2 + advice.phase() as u16,
                    },
                }
            }
        }

        state.serialize_field(
            "columns",
            &self
                .columns
                .iter()
                .cloned()
                .map(ColumnWrapper::from)
                .collect::<Box<[_]>>(),
        )?;
        state.serialize_field("perm_assembly", &self.perm_assembly)?;

        state.end()
    }
}
