//! Adapted from  https://github.com/microsoft/Nova/src/digest.rs
use bincode::Options;
use ff::PrimeField;
use serde::Serialize;
use sha3::{Digest, Sha3_256};
use std::io;
use std::marker::PhantomData;

use crate::constants::NUM_HASH_BITS;

/// Trait for components with potentially discrete digests to be included in their container's digest.
pub trait Digestible {
    /// Write the byte representation of Self in a byte buffer
    fn write_bytes<W: Sized + io::Write>(&self, byte_sink: &mut W) -> Result<(), io::Error>;
}

/// Marker trait to be implemented for types that implement `Digestible` and `Serialize`.
/// Their instances will be serialized to bytes then digested.
pub trait SimpleDigestible: Serialize {}

impl<T: SimpleDigestible> Digestible for T {
    fn write_bytes<W: Sized + io::Write>(&self, byte_sink: &mut W) -> Result<(), io::Error> {
        let config = bincode::DefaultOptions::new()
            .with_little_endian()
            .with_fixint_encoding();
        // Note: bincode recursively length-prefixes every field!
        config
            .serialize_into(byte_sink, self)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
    }
}

pub struct DigestComputer<'a, F: PrimeField, T> {
    inner: &'a T,
    _phantom: PhantomData<F>,
}

impl<'a, F: PrimeField, T: Digestible> DigestComputer<'a, F, T> {
    fn hasher() -> Sha3_256 {
        Sha3_256::new()
    }

    fn map_to_field(digest: &[u8]) -> F {
        let bv = (0..NUM_HASH_BITS.get()).map(|i| {
            let (byte_pos, bit_pos) = (i / 8, i % 8);
            let bit = (digest[byte_pos] >> bit_pos) & 1;
            bit == 1
        });

        // turn the bit vector into a scalar
        let mut digest = F::ZERO;
        let mut coeff = F::ONE;
        for bit in bv {
            if bit {
                digest += coeff;
            }
            coeff += coeff;
        }
        digest
    }

    /// Create a new `DigestComputer`
    pub fn new(inner: &'a T) -> Self {
        DigestComputer {
            inner,
            _phantom: PhantomData,
        }
    }

    /// Compute the digest of a `Digestible` instance.
    pub fn digest(&self) -> Result<F, io::Error> {
        let mut hasher = Self::hasher();
        self.inner
            .write_bytes(&mut hasher)
            .expect("Serialization error");
        let bytes: [u8; 32] = hasher.finalize().into();
        Ok(Self::map_to_field(&bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::{DigestComputer, SimpleDigestible};
    use ff::Field;
    use halo2curves::bn256::{Fr, G1Affine};
    use halo2curves::CurveAffine;
    use once_cell::sync::OnceCell;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize)]
    struct S<C: CurveAffine> {
        i: usize,
        #[serde(skip, default = "OnceCell::new")]
        digest: OnceCell<C::ScalarExt>,
    }

    impl<C: CurveAffine> SimpleDigestible for S<C> {}

    impl<C: CurveAffine> S<C> {
        fn new(i: usize) -> Self {
            S {
                i,
                digest: OnceCell::new(),
            }
        }

        fn digest(&self) -> C::ScalarExt {
            self.digest
                .get_or_try_init(|| DigestComputer::new(self).digest())
                .cloned()
                .unwrap()
        }
    }

    #[test]
    fn test_digest_field_not_ingested_in_computation() {
        let s1 = S::<G1Affine>::new(42);

        // let's set up a struct with a weird digest field to make sure the digest computation does not depend of it
        let oc = OnceCell::new();
        oc.set(Fr::ONE).unwrap();

        let s2: S<G1Affine> = S { i: 42, digest: oc };

        assert_eq!(
            DigestComputer::<Fr, _>::new(&s1).digest().unwrap(),
            DigestComputer::<Fr, _>::new(&s2).digest().unwrap()
        );

        // note: because of the semantics of `OnceCell::get_or_try_init`, the above
        // equality will not result in `s1.digest() == s2.digest`
        assert_ne!(
            s2.digest(),
            DigestComputer::<Fr, _>::new(&s2).digest().unwrap()
        );
    }

    #[test]
    fn test_digest_impervious_to_serialization() {
        let good_s = S::<G1Affine>::new(42);

        // let's set up a struct with a weird digest field to confuse deserializers
        let oc = OnceCell::new();
        oc.set(Fr::ONE).unwrap();

        let bad_s: S<G1Affine> = S { i: 42, digest: oc };
        // this justifies the adjective "bad"
        assert_ne!(good_s.digest(), bad_s.digest());

        let naughty_bytes = bincode::serialize(&bad_s).unwrap();

        let retrieved_s: S<G1Affine> = bincode::deserialize(&naughty_bytes).unwrap();
        assert_eq!(good_s.digest(), retrieved_s.digest())
    }
}
