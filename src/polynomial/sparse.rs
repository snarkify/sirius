// represent a sparse matrix M = {(i, j, v)}, i.e. M[i,j] = v
// the size of matrix is N*N with N = num_fixed_columns + num_instance_columns + num_advice_columns
pub(crate) type SparseMatrix<Scalar> = Vec<(usize, usize, Scalar)>;
