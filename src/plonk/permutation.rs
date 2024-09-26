//! Adapted from halo2/halo2_proofs/src/plonk/permutation/keygen.rs
use std::{cmp::Ordering, collections::HashSet, iter};

use halo2_proofs::{
    halo2curves::ff::PrimeField,
    plonk::{permutation::Argument, Any, Column, Error},
};
use serde::{Serialize, Serializer};
use tracing::*;

use crate::polynomial::sparse::SparseMatrix;

#[derive(Clone, Debug, PartialEq, Eq)]
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

        let mut columns_list = p.columns.clone();
        columns_list.sort_by(|lhs, rhs| match (lhs.column_type(), rhs.column_type()) {
            (Any::Instance, Any::Instance)
            | (Any::Advice(_), Any::Advice(_))
            | (Any::Fixed, Any::Fixed) => lhs.index().cmp(&rhs.index()),

            (Any::Instance, _) => Ordering::Greater,
            (Any::Advice(_), Any::Instance) => Ordering::Less,
            (Any::Advice(_), Any::Fixed) => Ordering::Greater,
            (Any::Fixed, _) => Ordering::Less,
        });

        // Before any equality constraints are applied, every cell in the permutation is
        // in a 1-cycle; therefore mapping and aux are identical, because every cell is
        // its own distinguished element.
        Assembly {
            columns: columns_list,
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

#[derive(Clone, PartialEq, Default)]
pub(crate) struct PermutationData {
    columns: Box<[Column<Any>]>,
    mapping: Box<[Vec<(usize, usize)>]>,
}

impl From<&Assembly> for PermutationData {
    fn from(assembly: &Assembly) -> Self {
        PermutationData {
            columns: assembly.columns.clone().into_boxed_slice(),
            mapping: assembly.mapping.clone().into_boxed_slice(),
        }
    }
}

impl PermutationData {
    pub fn matrix<F: PrimeField>(
        &self,
        k_table_size: usize,
        num_io: &[usize],
        num_advice_columns: usize,
    ) -> SparseMatrix<F> {
        construct_permutation_matrix(
            k_table_size,
            num_io,
            &self.columns,
            num_advice_columns,
            &self.mapping,
        )
    }

    #[instrument(level = "debug", skip_all)]
    /// Removes copy constraints for specific instance columns from the permutation mapping.
    ///
    /// # Parameters
    ///
    /// - `instance_columns_to_remove`: An iterator over the indices of instance columns
    ///   for which copy constraints need to be removed.
    ///
    /// # Returns
    ///
    /// A new `PermutationData` object with the specified copy constraints removed.
    ///
    /// # Algorithm
    ///
    /// 1. Identify the indices of all instance columns in the permutation and collect them in `instance_columns`.
    /// 2. Filter out and sort the indices to be removed that match the instance columns into `columns_to_remove_set`.
    /// 3. Iterate through each column in the permutation:
    ///    - If the column is in `columns_to_remove_set`:
    ///      - Reset its permutation by setting each of its mapping cells to the identity (i.e., `(column_index, row_index)`).
    ///    - Otherwise, for each row in the column:
    ///      - Traverse the cycle starting from the current cell. If a cycle includes a row in the columns to remove, bypass that row.
    ///      - Update the mapping to link directly to the next cell in the cycle that is not in the columns to remove.
    /// 4. Return the updated `PermutationData` object.
    pub(crate) fn rm_copy_constraints(
        mut self,
        instance_columns_to_remove: impl Iterator<Item = usize>,
    ) -> Self {
        let is_in_remove_set = {
            let instance_columns = self
                .columns
                .iter()
                .filter(|column| column.column_type().eq(&Any::Instance))
                .map(|column| column.index())
                .collect::<Box<[_]>>();
            debug!("instance_columns {instance_columns:?}");

            let mut columns_to_remove_set = instance_columns_to_remove
                .filter(|index| instance_columns.binary_search(index).is_ok())
                .collect::<Box<[_]>>();

            debug!("columns_to_remove_set {columns_to_remove_set:?}");

            columns_to_remove_set.sort();

            move |column: &Column<Any>| columns_to_remove_set.binary_search(&column.index()).is_ok()
        };

        for (column_index, column) in self.columns.iter().enumerate() {
            debug!("check column {column:?}");

            if is_in_remove_set(column) {
                continue;
            } else {
                debug!("start check permutations for column: {column:?}");
                let row_count = self.mapping[column_index].len();

                for row_index in 0..row_count {
                    let (mut next_i, mut next_j) = self.mapping[column_index][row_index];

                    let start = (column_index, row_index);
                    while (next_i, next_j) != start && is_in_remove_set(&self.columns[next_i]) {
                        debug!(
                            "{start:?}: finding tail without target-columns: {:?}",
                            (next_i, next_j)
                        );

                        (next_i, next_j) = if (next_i, next_j) == self.mapping[next_i][next_j] {
                            start
                        } else {
                            self.mapping[next_i][next_j]
                        };
                    }

                    debug!(
                        "mapping for [{column_index}][{row_index}] is {:?}",
                        (next_i, next_j)
                    );

                    self.mapping[column_index][row_index] = (next_i, next_j);
                }
            }
        }

        for (column_index, column) in self.columns.iter().enumerate() {
            debug!("check column {column:?}");

            if is_in_remove_set(column) {
                debug!("completely clearing all permutations for column: {column:?}");
                for (row_index, mapping_cell) in self.mapping[column_index].iter_mut().enumerate() {
                    *mapping_cell = (column_index, row_index);
                }
            }
        }

        self
    }
}

impl Serialize for PermutationData {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeStruct;

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
        state.serialize_field("perm_assembly", &self.mapping)?;

        state.end()
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
    perm_columns: &[Column<Any>],
    num_advice: usize,
    permutation_mapping: &[Vec<(usize, usize)>],
) -> SparseMatrix<F> {
    let num_rows = 1 << k_table_size;

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
    for (left_col, mapping_vec) in permutation_mapping.iter().enumerate() {
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

#[cfg(test)]
mod test {
    use std::{
        iter,
        mem::{self, MaybeUninit},
        ptr,
    };

    use halo2_proofs::{
        arithmetic::Field,
        halo2curves::pasta::Fq,
        plonk::{Advice, ColumnType},
    };
    use itertools::Itertools;
    use tracing::*;

    use super::*;
    use crate::polynomial::sparse;

    // Bypass the lack of a constructor for `Column`
    fn column<C: ColumnType>(index: usize, column_type: C) -> Column<C> {
        // Safety: just direct write to private field
        unsafe {
            // Allocate uninitialized memory for Column<C>
            let mut column_uninit: MaybeUninit<Column<C>> = MaybeUninit::uninit();
            let column_ptr = column_uninit.as_mut_ptr();

            // Manually write the `index` to its field
            // Note: This is safe since `index` is a public field
            ptr::write(&mut (*column_ptr).index as *mut usize, index);

            // To get the base pointer, cast to a pointer to the type containing the private fields
            // Then adjust the alignment by adding the size of the first `index` field (of type `usize`)
            let column_base_ptr = column_ptr as *mut u8;
            let column_type_offset = mem::size_of::<usize>();
            let column_type_ptr = column_base_ptr.add(column_type_offset) as *mut C;

            // Manually write the `column_type` to its field
            ptr::write(column_type_ptr, column_type);

            column_uninit.assume_init()
        }
    }

    #[test]
    fn column_hack() {
        let advice_col = column(0, Any::Advice(Advice::default()));

        assert_eq!(advice_col.index(), 0);
        assert_eq!(advice_col.column_type(), &Any::Advice(Advice::default()));

        let instance_col = column(0, Any::Instance);
        assert_eq!(instance_col.index(), 0);
        assert_eq!(instance_col.column_type(), &Any::Instance);

        let fixed_col = column(0, Any::Fixed);
        assert_eq!(fixed_col.index(), 0);
        assert_eq!(fixed_col.column_type(), &Any::Fixed);
    }

    const K_TABLE_SIZE: u32 = 3;
    const NUM_ROWS: usize = 8;
    const NUM_INSTANCES: usize = 10;
    const NUM_ADVICES: usize = 10;

    fn to_flat_column_offset(column: Column<Any>) -> usize {
        match column.column_type() {
            Any::Instance => column.index(),
            Any::Advice(_) => NUM_INSTANCES + column.index(),
            Any::Fixed => unreachable!("'fixed column' can't be a part of permutation"),
        }
    }

    fn to_flat_index(column: Column<Any>, row: usize, rows_len: &[usize]) -> usize {
        rows_len
            .iter()
            .take(to_flat_column_offset(column))
            .sum::<usize>()
            + row
    }

    fn check(permutation_data: &PermutationData, vec_Z: &[Fq]) -> bool {
        sparse::matrix_multiply(
            &permutation_data.matrix(
                K_TABLE_SIZE as usize,
                &iter::repeat(NUM_ROWS).take(NUM_INSTANCES).collect_vec(),
                NUM_ADVICES,
            ),
            vec_Z,
        )
        .into_iter()
        .zip_eq(vec_Z)
        .enumerate()
        .map(|(index, (y, z))| {
            let diff = y - z;

            warn!("mismatch at {index} with: {y:?} - {z:?} = {diff:?}");

            diff
        })
        .all(|f| f.is_zero_vartime())
    }

    fn random_Z() -> Vec<Fq> {
        let mut rng = rand::thread_rng();

        iter::repeat_with(|| Fq::random(&mut rng))
            .take((NUM_INSTANCES + NUM_ADVICES) * NUM_ROWS)
            .collect_vec()
    }

    #[tracing_test::traced_test]
    #[test]
    fn remove_copy_constraint() {
        let mut assembly = Assembly::new(
            NUM_ROWS,
            &Argument {
                columns: (0..NUM_INSTANCES)
                    .map(|index| column(index, Any::Instance))
                    .chain(
                        (0..NUM_ADVICES).map(|index| column(index, Any::Advice(Advice::default()))),
                    )
                    .collect(),
            },
        );

        let rows_len = iter::repeat(NUM_ROWS)
            .take(NUM_INSTANCES + NUM_ADVICES)
            .collect_vec();

        assembly
            .copy(column(0, Any::Instance), 0, column(1, Any::Instance), 0)
            .unwrap();

        let mut vec_Z = random_Z();

        assert!(
            !check(&((&assembly).into()), &vec_Z),
            "should fail: because value is random"
        );

        vec_Z[to_flat_index(column(0, Any::Instance), 0, &rows_len)] = Fq::ONE;
        vec_Z[to_flat_index(column(1, Any::Instance), 0, &rows_len)] = Fq::ONE;

        assert!(
            check(&((&assembly).into()), &vec_Z),
            "should pass, because value is equal"
        );

        // 0,0 -> 1,0 -> 2,0
        assembly
            .copy(column(1, Any::Instance), 0, column(2, Any::Instance), 0)
            .unwrap();

        // m[2,0] != ONE
        assert!(
            !check(&((&assembly).into()), &vec_Z),
            "should fail, because new copy-constraint not work"
        );

        let perm_data = PermutationData::from(&assembly).rm_copy_constraints(1..=1);

        // still m[2,0] != ONE
        assert!(
            !check(&perm_data, &vec_Z),
            "should fail: because even without first instance-column second columns is not equal"
        );

        vec_Z[to_flat_index(column(0, Any::Instance), 0, &rows_len)] = Fq::from_u128(10);
        vec_Z[to_flat_index(column(2, Any::Instance), 0, &rows_len)] = Fq::from_u128(10);

        assert!(
            check(&perm_data, &vec_Z),
            "should work: new copy constraint is work"
        );
    }

    #[tracing_test::traced_test]
    #[test]
    fn long_cycle() {
        let mut assembly = Assembly::new(
            NUM_ROWS,
            &Argument {
                columns: (0..NUM_INSTANCES)
                    .map(|index| column(index, Any::Instance))
                    .chain(
                        (0..NUM_ADVICES).map(|index| column(index, Any::Advice(Advice::default()))),
                    )
                    .collect(),
            },
        );

        let rows_len = iter::repeat(NUM_ROWS)
            .take(NUM_INSTANCES + NUM_ADVICES)
            .collect_vec();

        const CELLS: [(usize, usize); 9] = [
            (0, 0),
            (1, 0),
            (1, 1),
            (1, 2),
            (2, 0),
            (2, 1),
            (3, 0),
            (3, 1),
            (4, 0),
        ];

        for ((lhs_col, lhs_row), (rhs_col, rhs_row)) in CELLS.iter().tuple_windows() {
            assembly
                .copy(
                    column(*lhs_col, Any::Instance),
                    *lhs_row,
                    column(*rhs_col, Any::Instance),
                    *rhs_row,
                )
                .unwrap();
        }

        let mut vec_Z = random_Z();

        assert!(
            !check(&((&assembly).into()), &vec_Z),
            "should fail: because value is random"
        );

        for (col, row) in CELLS {
            vec_Z[to_flat_index(column(col, Any::Instance), row, &rows_len)] = Fq::ONE;
        }

        assert!(
            check(&((&assembly).into()), &vec_Z),
            "should pass, because value is equal"
        );

        let perm_data = PermutationData::from(&assembly).rm_copy_constraints(1..=3);

        let mut vec_Z = random_Z();
        vec_Z[to_flat_index(column(0, Any::Instance), 0, &rows_len)] = Fq::from_u128(10);
        vec_Z[to_flat_index(column(4, Any::Instance), 0, &rows_len)] = Fq::from_u128(10);

        assert!(
            check(&perm_data, &vec_Z),
            "should work: new copy constraint is work"
        );
    }
}
