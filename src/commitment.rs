use std::{io::Read, iter, ops};

use digest::{ExtendableOutput, Update};
use group::Curve;
use halo2_proofs::arithmetic::{best_multiexp, CurveAffine, CurveExt};
use log::*;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha3::Shake256;

use crate::util::parallelize;

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    #[error("Can't commit too long input: input len: {input_len}, but limit is {limit}")]
    TooLongInput { input_len: usize, limit: usize },
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct CommitmentKey<C: CurveAffine> {
    ck: Box<[C]>,
}

impl<C: CurveAffine> ops::Deref for CommitmentKey<C> {
    type Target = [C];

    fn deref(&self) -> &Self::Target {
        &self.ck
    }
}

impl<C: CurveAffine> CommitmentKey<C> {
    pub fn default_value() -> C {
        C::identity()
    }

    pub fn len(&self) -> usize {
        self.ck.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ck.is_empty()
    }

    pub fn setup(k: usize, label: &'static [u8]) -> Self {
        // This is usually a limitation on the curve, but we also want 32-bit
        // architectures to be supported.
        assert!(k < 32);
        let n: usize = 1 << k;

        let mut reader = Shake256::default().chain(label).finalize_xof();

        let ck_proj: Box<[_]> = iter::repeat_with(|| {
            let mut buffer = [0u8; 32];
            reader.read_exact(&mut buffer).unwrap();
            buffer
        })
        .take(n)
        .par_bridge()
        .map(|uniform_byte| (C::CurveExt::hash_to_curve("from_uniform_bytes"))(&uniform_byte))
        .collect();

        let mut ck: Box<[C]> = iter::repeat(C::identity()).take(n).collect();
        parallelize(&mut ck, |(ck, start)| {
            C::Curve::batch_normalize(&ck_proj[start..start + ck.len()], ck);
        });

        CommitmentKey { ck }
    }

    pub fn commit(&self, v: &[C::Scalar]) -> Result<C, Error> {
        if self.ck.len() >= v.len() {
            Ok(best_multiexp(v, &self.ck[..v.len()]).to_affine())
        } else {
            Err(Error::TooLongInput {
                input_len: v.len(),
                limit: self.ck.len(),
            })
        }
    }
}
