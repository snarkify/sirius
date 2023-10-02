use ff::PrimeField;

// represent a sparse matrix M = {(i, j, v)}, i.e. M[i,j] = v
// the size of matrix is N*N with N = num_fixed_columns + num_instance_columns + num_advice_columns
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
