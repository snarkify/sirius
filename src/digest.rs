use std::{io, iter, num::NonZeroUsize, ops::Deref};

use bincode::Options;
use bitter::{BitReader, LittleEndianReader};
use digest::{typenum::U32, Digest, OutputSizeUser};
use ff::{Field, PrimeField};
use halo2curves::CurveAffine;
use serde::Serialize;

pub use sha3::Sha3_256 as DefaultHasher;

use crate::constants::NUM_HASH_BITS;

/// A trait for converting a digest to a prime field element.
///
/// This trait is intended for use with types implementing the [`Digest`] trait,
/// allowing the conversion of a digest to an element of a prime field.
pub trait DigestToCurve: Digest {
    /// Serialize input & calculate digest & convert into [`CurveAffine`]
    //
    // Allows you to use any hash function whose output is of size `[u8; 32]`
    //
    fn digest_to_curve<C: CurveAffine>(input: &impl Serialize) -> Result<C, io::Error>
    where
        Self: OutputSizeUser<OutputSize = U32>,
    {
        // Because [rust#92827](https://github.com/rust-lang/rust/issues/92827)
        // we can't explicitly limit `F::NUM_BITS = 32` as generic params
        if C::ScalarExt::NUM_BITS > 32 * 8 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Field representation too big for this hash function, {} but expected < 32 * 8",
                    C::ScalarExt::NUM_BITS
                ),
            ));
        }

        let digest = Self::digest(
            bincode::DefaultOptions::new()
                .with_little_endian()
                .with_fixint_encoding()
                .serialize(input)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?,
        );

        Ok(into_curve_by_bits(digest.deref(), NUM_HASH_BITS))
    }
}
impl DigestToCurve for sha3::Sha3_256 {}

fn into_curve_by_bits<C: CurveAffine>(input: &[u8], bits_count: NonZeroUsize) -> C {
    let mut coeff = C::ScalarExt::ONE;

    let mut reader = LittleEndianReader::new(input);
    let scalar = iter::repeat_with(|| reader.read_bit())
        .map_while(|b| b)
        .take(bits_count.get())
        .fold(C::ScalarExt::ZERO, |mut result, bit| {
            if bit {
                result += coeff;
            }

            coeff = coeff.double();

            result
        });
    C::generator().mul(scalar).into()
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use ff::PrimeField;
    use halo2curves::bn256::{Fr, G1Affine};
    use serde::*;

    use super::{into_curve_by_bits, DigestToCurve};

    #[test]
    fn consistency() {
        // MODULUS - 1
        let input = Fr::from_str_vartime(
            "21888242871839275222246405745257275088548364400416034343698204186575808495616",
        )
        .unwrap();

        assert_eq!(
            into_curve_by_bits::<G1Affine>(
                &input.to_repr(),
                NonZeroUsize::new(Fr::NUM_BITS as usize).unwrap()
            ),
            -G1Affine::generator()
        );
    }

    /// A test structure for demonstration purposes.
    #[derive(Serialize)]
    struct TestStruct {
        bytes: Vec<u8>,
        num: u128,
        s: String,
    }

    /// Tests successful conversion of a hash to a prime field element.
    #[test]
    fn test_digest_to_curve_conversion() {
        let test_data = TestStruct {
            bytes: vec![100; 100],
            num: u128::MAX,
            s: "string".into(),
        };

        let _result = sha3::Sha3_256::digest_to_curve::<G1Affine>(&test_data)
            .expect("Failed to convert digest to field element");
    }

    /// Tests conversion with an empty input.
    #[test]
    fn test_empty_input_conversion() {
        let test_data = TestStruct {
            bytes: vec![],
            num: 0,
            s: "".into(),
        };

        let _result = sha3::Sha3_256::digest_to_curve::<G1Affine>(&test_data)
            .expect("Failed to convert digest to field element for empty input");
    }

    #[test]
    fn skip_field() {
        #[derive(Serialize)]
        struct Foo {
            num: u32,
        }

        #[derive(Serialize)]
        struct Boo {
            num: u32,
            #[serde(skip)]
            skipme: String,
        }

        let foo = sha3::Sha3_256::digest_to_curve::<G1Affine>(&Foo { num: 32 })
            .expect("Failed to convert digest to field element for empty input");

        let boo = sha3::Sha3_256::digest_to_curve::<G1Affine>(&Boo {
            num: 32,
            skipme: "data".to_string(),
        })
        .expect("Failed to convert digest to field element for empty input");

        assert_eq!(foo, boo);
    }
}
