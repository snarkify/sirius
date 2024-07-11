use crate::ff::PrimeField;

// represent a sparse matrix M = {(i, j, v)}, i.e. M[i,j] = v
// the size of matrix is N*N with N = num_io + num_advice_columns * num_rows
pub(crate) type SparseMatrix<Scalar> = Vec<(usize, usize, Scalar)>;

pub(crate) fn matrix_multiply<F: PrimeField>(P: &SparseMatrix<F>, Z: &[F]) -> Vec<F> {
    let N = Z.len();
    let mut result: Vec<F> = vec![F::ZERO; N];

    for (row, col, value) in P {
        if *col < Z.len() {
            result[*row] += *value * Z[*col];
        } else {
            panic!("invalid matrix multiply");
        }
    }
    result
}
