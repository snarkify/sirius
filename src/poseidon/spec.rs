use std::ops;

use ff::FromUniformBytes;
use serde::Serialize;

#[derive(Clone, Debug)]
pub struct Spec<F: ff::PrimeField, const T: usize, const RATE: usize>(
    pub poseidon::Spec<F, T, RATE>,
);

impl<F: ff::PrimeField, const T: usize, const RATE: usize> Spec<F, T, RATE>
where
    F: FromUniformBytes<64>,
{
    pub fn new(r_f: usize, r_p: usize) -> Self {
        Self(poseidon::Spec::new(r_f, r_p))
    }
}

impl<F: ff::PrimeField, const T: usize, const RATE: usize> ops::Deref for Spec<F, T, RATE> {
    type Target = poseidon::Spec<F, T, RATE>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: Serialize + ff::PrimeField, const T: usize, const RATE: usize> Serialize
    for Spec<F, T, RATE>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        #[derive(Serialize)]
        struct SerializableArray<F: Serialize, const T: usize>(
            #[serde(with = "serde_arrays")] [F; T],
        );

        #[derive(Serialize)]
        struct SerializableMDSMatrix<F: Serialize, const T: usize, const RATE: usize> {
            #[serde(with = "serde_arrays")]
            rows: [SerializableArray<F, T>; T],
        }

        #[derive(Serialize)]
        struct SerializableSparseMDSMatrix<F: Serialize, const T: usize, const RATE: usize> {
            row: SerializableArray<F, T>,
            col_hat: SerializableArray<F, RATE>,
        }

        #[derive(Serialize)]
        struct SerializableMDSMatrices<F: Serialize, const T: usize, const RATE: usize> {
            mds: SerializableMDSMatrix<F, T, RATE>,
            pre_sparse_mds: SerializableMDSMatrix<F, T, RATE>,
            sparse_matrices: Box<[SerializableSparseMDSMatrix<F, T, RATE>]>,
        }

        #[derive(Serialize)]
        struct SerializableOptimizedConstants<F: Serialize, const T: usize> {
            start: Box<[SerializableArray<F, T>]>,
            partial: Box<[F]>,
            end: Box<[SerializableArray<F, T>]>,
        }
        // Create a struct to hold serializable representations of Spec fields
        #[derive(Serialize)]
        struct SerializableSpec<F: Serialize, const T: usize, const RATE: usize> {
            r_f: usize,
            mds_matrices: SerializableMDSMatrices<F, T, RATE>,
            constants: SerializableOptimizedConstants<F, T>,
        }

        let poseidon_spec = &self.0;
        let r_f = poseidon_spec.r_f();
        let mds_rows = poseidon_spec.mds_matrices().mds().rows();

        let mds = SerializableMDSMatrix {
            rows: mds_rows.map(SerializableArray),
        };

        let pre_sparse_mds = SerializableMDSMatrix {
            rows: poseidon_spec
                .mds_matrices()
                .pre_sparse_mds()
                .rows()
                .map(|m| SerializableArray(m)),
        };

        let mds_matrices = SerializableMDSMatrices {
            mds,
            pre_sparse_mds,
            sparse_matrices: poseidon_spec
                .mds_matrices()
                .sparse_matrices()
                .iter()
                .map(|sparse_matrix| SerializableSparseMDSMatrix {
                    row: SerializableArray(*sparse_matrix.row()),
                    col_hat: SerializableArray(*sparse_matrix.col_hat()),
                })
                .collect::<Box<[_]>>(),
        };

        let constants = SerializableOptimizedConstants {
            start: poseidon_spec
                .constants()
                .start()
                .iter()
                .copied()
                .map(SerializableArray)
                .collect(),
            partial: poseidon_spec
                .constants()
                .partial()
                .iter()
                .copied()
                .collect(),
            end: poseidon_spec
                .constants()
                .end()
                .iter()
                .copied()
                .map(SerializableArray)
                .collect(),
        };

        SerializableSpec {
            r_f,
            mds_matrices,
            constants,
        }
        .serialize(serializer)
    }
}

#[cfg(test)]
mod tests {
    use halo2curves::secp256r1::Fp;
    use tracing_test::traced_test;

    use super::*;

    #[traced_test]
    #[test]
    fn just_serialize() {
        let spec = Spec::<Fp, 10, 9>::new(10, 10);
        bincode::serialize(&spec).unwrap();
    }
}
