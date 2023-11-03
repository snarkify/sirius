use ff::{BatchInvert, Field, PrimeField};
use halo2_proofs::plonk::Assigned;
use num_bigint::BigUint;
pub(crate) use rayon::current_num_threads;

pub fn bytes_to_bits_le(bytes: Vec<u8>) -> Vec<bool> {
    let mut bits = Vec::new();

    for byte in &bytes {
        // Add bits of each byte to the BitVec
        for i in 0..8 {
            let mask = 1 << i;
            bits.push((byte & mask) != 0);
        }
    }
    bits
}

pub fn bits_to_bytes_le(bits: Vec<bool>) -> Vec<u8> {
    let mut bytes = Vec::new();
    for chunk in bits.chunks(8) {
        let mut byte = 0u8;
        for (i, &bit) in chunk.iter().enumerate() {
            if bit {
                byte |= 1 << i;
            }
        }
        bytes.push(byte);
    }
    bytes
}

pub fn fe_to_bits_le<F: PrimeField>(fe: &F) -> Vec<bool> {
    let big = fe_to_big(fe);
    let bytes = big.to_bytes_le();
    bytes_to_bits_le(bytes)
}

pub fn bits_to_fe_le<F: PrimeField>(bits: Vec<bool>) -> F {
    let bytes = bits_to_bytes_le(bits);
    let mut repr = F::Repr::default();
    assert!(bytes.len() <= repr.as_ref().len());
    repr.as_mut()[..bytes.len()].clone_from_slice(bytes.as_slice());
    F::from_repr(repr).unwrap()
}

pub fn modulus<F: PrimeField>() -> BigUint {
    fe_to_big(&(-F::ONE)) + 1usize
}

pub fn fe_from_big<F: PrimeField>(big: BigUint) -> Option<F> {
    let bytes = big.to_bytes_le();
    let mut repr = F::Repr::default();

    if bytes.len() > repr.as_ref().len() {
        return None;
    }

    repr.as_mut()[..bytes.len()].clone_from_slice(bytes.as_slice());

    F::from_repr(repr).into()
}

pub fn fe_to_big<F: PrimeField>(fe: &F) -> BigUint {
    BigUint::from_bytes_le(fe.to_repr().as_ref())
}

pub fn fe_to_fe<F1: PrimeField, F2: PrimeField>(fe: &F1) -> Option<F2> {
    fe_from_big(fe_to_big(fe) % modulus::<F2>())
}

pub fn fe_to_fe_safe<F1: PrimeField, F2: PrimeField>(fe: &F1) -> Option<F2> {
    let bn1 = fe_to_big(fe);

    if bn1 >= modulus::<F2>() {
        None
    } else {
        fe_from_big(bn1)
    }
}

fn invert<F: Field>(
    poly: &Vec<Assigned<F>>,
    inv_denoms: impl Iterator<Item = F> + ExactSizeIterator,
) -> Vec<F> {
    assert_eq!(inv_denoms.len(), poly.len());
    poly.iter()
        .zip(inv_denoms)
        .map(|(a, inv_den)| a.numerator() * inv_den)
        .collect()
}

pub(crate) fn batch_invert_assigned<F: Field>(assigned: &[Vec<Assigned<F>>]) -> Vec<Vec<F>> {
    let mut assigned_denominators: Vec<_> = assigned
        .iter()
        .map(|f| {
            f.iter()
                .map(|value| value.denominator())
                .collect::<Vec<_>>()
        })
        .collect();

    assigned_denominators
        .iter_mut()
        .flat_map(|f| {
            f.iter_mut()
                // If the denominator is trivial, we can skip it, reducing the
                // size of the batch inversion.
                .filter_map(|d| d.as_mut())
        })
        .batch_invert();

    assigned
        .iter()
        .zip(assigned_denominators)
        .map(|(poly, inv_denoms)| invert(poly, inv_denoms.into_iter().map(|d| d.unwrap_or(F::ONE))))
        .collect()
}

pub fn parallelize_iter<I, T, F>(iter: I, f: F)
where
    I: Send + Iterator<Item = T>,
    T: Send,
    F: Fn(T) + Send + Sync + Clone,
{
    rayon::scope(|scope| {
        for item in iter {
            let f = f.clone();
            scope.spawn(move |_| f(item));
        }
    });
}

/// This simple utility function will parallelize an operation that is to be
/// performed over a mutable slice.
pub fn parallelize<T, F>(v: &mut [T], f: F)
where
    T: Send,
    F: Fn((&mut [T], usize)) + Send + Sync + Clone,
{
    let num_threads = current_num_threads();
    let chunk_size = (v.len() as f64 / num_threads as f64).ceil() as usize;
    if v.len() < num_threads {
        f((v, 0));
    } else {
        parallelize_iter(v.chunks_mut(chunk_size).zip((0..).step_by(chunk_size)), f);
    }
}

pub(crate) fn trim_leading_zeros(hex: String) -> String {
    let without_prefix = hex.as_str().trim_start_matches("0x");
    let trimmed = without_prefix.trim_start_matches('0');
    format!("0x{}", trimmed)
}

pub(crate) fn normalize_trailing_zeros(bits: &mut Vec<bool>, bit_len: usize) {
    let last_one_position = bits
        .iter()
        .enumerate()
        .rev()
        .find_map(|(idx, &value)| value.then_some(idx));

    if let Some(position) = last_one_position {
        bits.truncate(position + 1);
    } else {
        bits.truncate(1);
    }

    let length = bits.len();
    assert!(bit_len >= length, "bit length exceed maximum value");

    for _ in 0..(bit_len - length) {
        bits.push(false);
    }
}
