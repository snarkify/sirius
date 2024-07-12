use std::{
    fs::{self, File},
    io::{self, Read, Write},
    iter, ops,
    ops::Not,
    path::Path,
    slice,
};

use digest::{ExtendableOutput, Update};
use halo2_proofs::{
    arithmetic::{CurveAffine, CurveExt},
    halo2curves::msm::best_multiexp,
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha3::Shake256;
use some_to_err::*;
use tracing::*;

use crate::{group::Curve, util::parallelize};

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

impl<C: CurveAffine> CommitmentKey<C> {
    /// Saves `Self` as memory cast to a file.
    /// Fast, but takes up a lot of memory.
    ///
    /// # Safety
    /// Check [`std::slice::from_raw_parts`] for details
    pub unsafe fn save_to_file(&self, file_path: &Path) -> io::Result<()> {
        let ptr = self.ck.as_ptr();
        let len = self.ck.len();
        let byte_slice = slice::from_raw_parts(ptr as *const u8, len * std::mem::size_of::<C>());
        File::create(file_path)?.write_all(byte_slice)
    }

    /// Load `Self` from memory cast at file.
    /// Fast, but unsafe
    ///
    /// # Safety
    /// - Safe only if the file is created with [`CommitmentKey::save_to_file`]
    /// - Check [`std::slice::from_raw_parts_mut`] for details
    pub unsafe fn load_from_file(file_path: &Path, k: usize) -> io::Result<Self> {
        let vec_len: usize = 1 << k;

        let mut ck = Vec::with_capacity(vec_len);
        let byte_slice = slice::from_raw_parts_mut(
            ck.as_mut_ptr() as *mut u8,
            vec_len * std::mem::size_of::<C>(),
        );

        File::open(file_path)?.read_exact(byte_slice)?;
        ck.set_len(vec_len);

        Ok(Self {
            ck: ck.into_boxed_slice(),
        })
    }

    /// Load or if missing setup and store commitment key in `cache_folder`
    ///
    /// The rule for the name is that for each `label`, a subfolder is created where all keys named
    /// `{k}.bin`, where `k` is the size of key
    ///
    /// # Safety
    /// - Safe only if the cache file is created with [`CommitmentKey::save_to_file`]
    /// - Check [`std::slice::from_raw_parts`] & [`std::slice::from_raw_parts_mut`] for details
    pub unsafe fn load_or_setup_cache(
        cache_folder: &Path,
        label: &'static str,
        k: usize,
    ) -> io::Result<Self> {
        let file_path = cache_folder.join(label).join(format!("{k}.bin"));

        if file_path.exists() {
            info!("{file_path:?} exists, load key");
            let key = unsafe { Self::load_from_file(&file_path, k) }?;

            key.par_iter()
                .all(|p: &C| p.is_on_curve().into())
                .not()
                .then(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Wrong file in cache, some ptr out of curve",
                    )
                })
                .err_or(key)
        } else {
            info!("{file_path:?} not exists, start generate");
            let key = Self::setup(k, label.as_bytes());

            fs::create_dir_all(file_path.parent().unwrap())?;

            unsafe {
                key.save_to_file(&file_path)?;
            }

            Ok(key)
        }
    }
}

#[cfg(test)]
mod file_tests {
    use tempfile::tempdir;
    use tracing_test::traced_test;

    use super::*;
    use crate::halo2curves::bn256::G1Affine;

    #[traced_test]
    #[test]
    fn consistency() {
        const K: usize = 10;

        let key = CommitmentKey::<G1Affine>::setup(K, b"");
        let dir = tempdir().unwrap();
        let file_path = dir.path().join("my-temporary-note.txt");

        unsafe {
            key.save_to_file(&file_path).unwrap();
        }

        let loaded = unsafe { CommitmentKey::load_from_file(&file_path, K).unwrap() };

        assert_eq!(key, loaded);
    }
}
