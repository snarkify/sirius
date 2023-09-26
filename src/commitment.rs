use std::{io::Read, iter};

use group::Curve;
use halo2_proofs::arithmetic::{best_multiexp, CurveAffine, CurveExt};
use rayon::prelude::*;
use sha3::{
    digest::{ExtendableOutput, Input},
    Shake256,
};

use crate::util::parallelize;

#[derive(Clone, Debug)]
pub struct CommitmentKey<C: CurveAffine> {
    ck: Vec<C>,
}

impl<C: CurveAffine> CommitmentKey<C> {
    pub fn default_value() -> C {
        C::identity()
    }

    pub fn setup(k: usize, label: &'static [u8]) -> Self {
        // This is usually a limitation on the curve, but we also want 32-bit
        // architectures to be supported.
        assert!(k < 32);
        let n: usize = 1 << k;

        let mut shake = Shake256::default();
        shake.input(label);
        let mut reader = shake.xof_result();

        let ck_proj: Vec<_> = iter::repeat_with(|| {
            let mut uniform_bytes = [0u8; 32];
            reader.read_exact(&mut uniform_bytes).unwrap();
            uniform_bytes
        })
        .take(n)
        .par_bridge()
        .map(|uniform_byte| (C::CurveExt::hash_to_curve("from_uniform_bytes"))(&uniform_byte))
        .collect();

        let mut ck: Vec<C> = vec![C::identity(); n];
        parallelize(&mut ck, |(ck, start)| {
            C::Curve::batch_normalize(&ck_proj[start..start + ck.len()], ck);
        });

        CommitmentKey { ck }
    }

    pub fn commit(&self, v: &[C::Scalar]) -> C {
        assert!(
            self.ck.len() >= v.len(),
            "CommitmentKey size must be greater than or equal to scalar vector size"
        );
        best_multiexp(v, &self.ck[..v.len()]).to_affine()
    }
}
