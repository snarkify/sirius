use group::Curve;
use halo2_proofs::arithmetic::{best_multiexp, CurveAffine, CurveExt};
use rayon::prelude::*;
use sha3::digest::{ExtendableOutput, Input};
use sha3::Shake256;
use std::io::Read;

use crate::util::parallelize;

#[derive(Clone, Debug)]
pub struct CommitmentKey<C: CurveAffine> {
    ck: Vec<C>,
}

impl<C: CurveAffine> CommitmentKey<C> {
    pub fn setup(k: usize, label: &'static [u8]) -> Self {
        // This is usually a limitation on the curve, but we also want 32-bit
        // architectures to be supported.
        assert!(k < 32);
        let n: usize = 1 << k;

        let mut shake = Shake256::default();
        shake.input(label);
        let mut reader = shake.xof_result();
        let mut uniform_bytes_vec = Vec::new();
        for _ in 0..n {
            let mut uniform_bytes = [0u8; 32];
            reader.read_exact(&mut uniform_bytes).unwrap();
            uniform_bytes_vec.push(uniform_bytes);
        }
        let ck_proj: Vec<_> = (0..n)
            .collect::<Vec<usize>>()
            .into_par_iter()
            .map(|i| {
                let hash = C::CurveExt::hash_to_curve("from_uniform_bytes");
                hash(&uniform_bytes_vec[i])
            })
            .collect();

        let mut ck: Vec<C> = vec![C::identity(); n];
        parallelize(&mut ck, |(ck, start)| {
            C::Curve::batch_normalize(&ck_proj[start..start + ck.len()], ck);
        });

        CommitmentKey { ck }
    }

    pub fn commit(&self, v: &[C::Scalar]) -> C {
        best_multiexp(v, &self.ck).to_affine()
    }
}
