use std::{io::BufReader, iter, mem};

use digest::{ExtendableOutput, Update};
use group::Curve;
use halo2_proofs::arithmetic::{best_multiexp, CurveAffine, CurveExt};
use log::*;
use rayon::prelude::*;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sha3::Shake256;

use crate::util::parallelize;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommitmentKey<C: CurveAffine> {
    ck: Box<[C]>,
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

    pub fn commit(&self, v: &[C::Scalar]) -> Option<C> {
        if self.ck.len() < v.len() {
            return None;
        }
        Some(best_multiexp(v, &self.ck[..v.len()]).to_affine())
    }
}

use std::{
    fs::File,
    io::{self, Read, Write},
    path::Path,
};

impl<C: CurveAffine + Serialize + DeserializeOwned> CommitmentKey<C> {
    pub fn save_to_file(&self, file_path: &Path) -> io::Result<()> {
        File::create(file_path)?.write_all(
            &bincode::serialize(self)
                .map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))?,
        )
    }

    pub fn load_from_file(file_path: &Path) -> io::Result<Self> {
        let mut file = BufReader::new(File::open(file_path)?);

        // Read the initial usize
        let mut usize_buffer = [0u8; mem::size_of::<usize>()];
        file.read_exact(&mut usize_buffer)?;
        let _size = usize::from_le_bytes(usize_buffer);

        let chunks: Box<[_]> = iter::repeat_with(|| {
            let mut buffer = [0u8; 32];
            file.read_exact(&mut buffer).ok()?;
            Some(buffer)
        })
        .map_while(|b| b)
        .collect();

        debug!("chunk collected");

        Ok(CommitmentKey {
            ck: chunks
                .into_par_iter()
                .map(|chunk| unsafe { *(chunk.as_ptr() as *const C) })
                .collect::<Box<[C]>>(),
        })
    }
}
