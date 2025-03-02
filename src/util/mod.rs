use std::{fmt, iter, num::NonZeroUsize};

use halo2_proofs::{
    halo2curves::{
        ff::{FromUniformBytes, PrimeFieldBits},
        CurveAffine,
    },
    plonk::Assigned,
};
use itertools::Itertools;
use num_bigint::BigUint;
pub(crate) use rayon::current_num_threads;
use rayon::prelude::*;

use crate::{
    ff::{BatchInvert, Field, PrimeField},
    main_gate::AssignedValue,
    poseidon::{PoseidonHash, ROTrait, Spec},
};

pub mod mock_prover;

pub use mock_prover::MockProver;

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

pub trait ScalarToBase: CurveAffine {
    fn scalar_to_base(input: &Self::Scalar) -> Option<Self::Base>;
}
impl<C: CurveAffine> ScalarToBase for C {
    fn scalar_to_base(input: &C::Scalar) -> Option<C::Base> {
        fe_to_fe(input)
    }
}

pub trait BaseToScalar: CurveAffine {
    fn base_to_scalar(input: &Self::Base) -> Option<Self::Scalar>;
}
impl<C: CurveAffine> BaseToScalar for C {
    fn base_to_scalar(input: &Self::Base) -> Option<Self::Scalar> {
        fe_to_fe(input)
    }
}

pub fn fe_to_fe_safe<F1: PrimeField, F2: PrimeField>(fe: &F1) -> Option<F2> {
    let bn1 = fe_to_big(fe);
    let bn2 = modulus::<F2>();

    if bn1 >= bn2 {
        None
    } else {
        fe_from_big(bn1)
    }
}

fn invert<F: Field>(poly: &[Assigned<F>], inv_denoms: impl ExactSizeIterator<Item = F>) -> Vec<F> {
    assert_eq!(inv_denoms.len(), poly.len());
    poly.iter()
        .zip(inv_denoms)
        .map(|(a, inv_den)| a.numerator() * inv_den)
        .collect()
}

pub(crate) fn batch_invert_assigned<F: Field>(assigned: &[Vec<Assigned<F>>]) -> Vec<Vec<F>> {
    let mut assigned_denominators: Vec<_> = assigned
        .par_iter()
        .map(|f| {
            f.par_iter()
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

pub(crate) fn normalize_trailing_zeros(bits: &mut Vec<bool>, bit_len: NonZeroUsize) {
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
    assert!(bit_len.get() >= length, "bit length exceed maximum value");

    for _ in 0..(bit_len.get() - length) {
        bits.push(false);
    }
}

/// Concatenates a slice of vectors, each containing elements of type `F`, into a single vector,
/// with padding to ensure uniform segment sizes.
pub(crate) fn concatenate_with_padding<F: PrimeField>(vs: &[Vec<F>], pad_size: usize) -> Vec<F> {
    vs.par_iter()
        .flat_map_iter(|v| v.iter().copied().pad_using(pad_size, |_| F::ZERO))
        .collect()
}

#[allow(clippy::items_after_test_module)]
#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;
    use crate::halo2curves::pasta::Fp;

    // Helper to easily create an Fp element
    fn fp(num: u64) -> Fp {
        Fp::from(num)
    }

    // Test empty input
    #[traced_test]
    #[test]
    fn concatenate_empty() {
        let input: Vec<Vec<Fp>> = vec![];
        let result = concatenate_with_padding(&input, 4);
        assert!(result.is_empty());
    }

    // Test padding with single vector
    #[test]
    fn single_vector_with_padding() {
        let input = vec![vec![fp(1), fp(2)]];
        let result = concatenate_with_padding(&input, 4);
        assert_eq!(result, vec![fp(1), fp(2), Fp::zero(), Fp::zero()]);
    }

    // Test no padding needed (perfect fit)
    #[test]
    fn single_vector_no_padding() {
        let input = vec![vec![fp(1), fp(2), fp(3), fp(4)]];
        let result = concatenate_with_padding(&input, 4);
        assert_eq!(result, vec![fp(1), fp(2), fp(3), fp(4)]);
    }

    // Test padding with multiple vectors
    #[test]
    fn multiple_vectors_with_padding() {
        let input = vec![vec![fp(1), fp(2)], vec![fp(3)], vec![fp(4), fp(5), fp(6)]];
        let pad_size = 4;

        assert_eq!(
            concatenate_with_padding(&input, pad_size),
            [
                fp(1),
                fp(2),
                Fp::zero(),
                Fp::zero(), // First vector with padding
                fp(3),
                Fp::zero(),
                Fp::zero(),
                Fp::zero(), // Second vector with padding
                fp(4),
                fp(5),
                fp(6),
                Fp::zero(), // Third vector with padding
            ]
        );
    }

    // Test with pad_size = 1 (should mirror input exactly)
    #[test]
    fn pad_size_one() {
        assert_eq!(
            concatenate_with_padding(&[vec![fp(1)], vec![fp(2), fp(3)]], 1),
            [fp(1), fp(2), fp(3)]
        );
    }
}

pub(crate) fn create_ro<F, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>(
) -> PoseidonHash<F, T, RATE>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    let spec = Spec::<F, T, RATE>::new(R_F, R_P);
    PoseidonHash::<F, T, RATE>::new(spec)
}

/// Concatenate N vectors
#[macro_export]
macro_rules! concat_vec {
    ($($x:expr),*) => {{
        let mut total_capacity = 0;
        $(
            total_capacity += $x.len();
        )*
        let mut new_vec = Vec::with_capacity(total_capacity);
        $(
            new_vec.extend_from_slice($x);
        )*
        new_vec
    }};
}

/// A macro used for MockProver certain circuit by leveraging halo2_proofs.
#[macro_export]
macro_rules! run_mock_prover_test {
    ($k:expr, $circuit:expr, $public_inputs:expr) => {
        use halo2_proofs::dev::MockProver;

        let prover = match MockProver::run($k, &$circuit, $public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("MockProver meet error when k is {:?}, {:#?}", $k, e),
        };
        assert_eq!(prover.verify(), Ok(()));
    };
}

/// A macro used for create and verify proof for certain circuit by leveraging halo2_proofs.
/// Including three phases:
///     1. setup: generate param, verify key, prove key
///     2. prove: generate proof
///     3. verify: verify proof
///
/// For now, it only supports IPA commitment scheme.
#[macro_export]
macro_rules! create_and_verify_proof {
    (IPA, $k:expr, $circuit:expr, $public_inputs:expr, $curve_point:ident) => {{
        use halo2_proofs::{
            plonk::{create_proof, keygen_pk, keygen_vk, verify_proof},
            poly::{
                commitment::ParamsProver,
                ipa::{
                    commitment::{IPACommitmentScheme, ParamsIPA},
                    multiopen::ProverIPA,
                    strategy::SingleStrategy,
                },
                VerificationStrategy,
            },
            transcript::{
                Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer,
                TranscriptWriterBuffer,
            },
        };
        use rand_core::OsRng;

        // setup
        let params: ParamsIPA<$curve_point> = ParamsIPA::<$curve_point>::new($k);
        let vk = keygen_vk(&params, &$circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &$circuit).expect("keygen_pk should not fail");

        // prove
        let mut transcript = Blake2bWrite::<_, $curve_point, Challenge255<_>>::init(vec![]);
        create_proof::<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>(
            &params,
            &pk,
            &[$circuit],
            &[$public_inputs],
            OsRng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        // verify
        let proof = transcript.finalize();
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&params);
        verify_proof(
            &params,
            pk.get_vk(),
            strategy,
            &[$public_inputs],
            &mut transcript,
        )
        .unwrap();

        proof
    }};
}

pub(crate) fn get_power_of_two_iter<F: PrimeField>() -> impl Iterator<Item = F> {
    iter::successors(Some(F::ONE), |l| Some(l.double()))
}

pub(crate) struct CellsValuesView<'l, F: PrimeField> {
    cells: &'l [AssignedValue<F>],
}

impl<'l, F: PrimeField> From<&'l [AssignedValue<F>]> for CellsValuesView<'l, F> {
    fn from(value: &'l [AssignedValue<F>]) -> Self {
        Self { cells: value }
    }
}
impl<F: PrimeField> fmt::Debug for CellsValuesView<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Cells: [")?;

        if let Some(cells_values) = self
            .cells
            .iter()
            .map(|cell| cell.value().unwrap().cloned())
            .collect::<Option<Vec<_>>>()
        {
            write!(f, "{:?}", cells_values)?;
        } else {
            write!(f, "empty")?;
        }

        write!(f, "]")
    }
}

pub mod try_multi_product {
    /// This module provides utilities to create an iterator that yields the cartesian product of nested iterators.
    ///
    /// It is similar to [`itertools::Itertools::multi_cartesian_product`] but operates in a more
    /// simplified manner without requiring `Clone` and [`Result`] inside
    ///
    /// A trait to extend iterators with the `try_multi_product` method.
    pub trait TryMultiProduct<T, I: Iterator<Item = Result<T, E>>, E>:
        Iterator<Item = I> + Sized
    {
        /// # Example
        ///
        /// ```
        /// use crate::sirius::util::TryMultiProduct;
        ///
        /// let iterators = vec![
        ///     vec![Result::<_, ()>::Ok(1), Ok(2), Ok(3)].into_iter(),
        ///     vec![Ok(4), Ok(5)].into_iter(),
        ///     vec![Ok(6), Ok(7)].into_iter(),
        /// ];
        ///
        /// let mut multi_prod = iterators.into_iter().try_multi_product();
        ///
        /// assert_eq!(multi_prod.next(), Some(Ok(vec![1, 4, 6].into_boxed_slice())));
        /// assert_eq!(multi_prod.next(), Some(Ok(vec![2, 5, 7].into_boxed_slice())));
        /// assert_eq!(multi_prod.next(), None);
        /// ```
        fn try_multi_product(self) -> MultiProductWithResults<T, I, E> {
            MultiProductWithResults::from_iter(self)
        }
    }
    impl<MI, T, I, E> TryMultiProduct<T, I, E> for MI
    where
        I: Iterator<Item = Result<T, E>>,
        MI: Iterator<Item = I> + Sized,
    {
    }

    pub struct MultiProductWithResults<T, I: Iterator<Item = Result<T, E>>, E> {
        iterators: Box<[I]>,
    }

    impl<T, I: Iterator<Item = Result<T, E>>, E> FromIterator<I> for MultiProductWithResults<T, I, E> {
        fn from_iter<IN: IntoIterator<Item = I>>(iter: IN) -> Self {
            Self {
                iterators: iter.into_iter().collect(),
            }
        }
    }
    impl<T, E, I: Iterator<Item = Result<T, E>>> Iterator for MultiProductWithResults<T, I, E> {
        type Item = Result<Box<[T]>, E>;

        fn next(&mut self) -> Option<Result<Box<[T]>, E>> {
            let len = self.iterators.len();

            Some(
                self.iterators
                    .iter_mut()
                    .map(|i| i.next())
                    .try_fold(Ok(Vec::with_capacity(len)), |acc, next_value| {
                        match (acc, next_value) {
                            (Ok(mut acc), Some(Ok(next_value))) => {
                                acc.push(next_value);
                                Some(Ok(acc))
                            }
                            (Err(err), _) | (_, Some(Err(err))) => Some(Err(err)),
                            (_, None) => None,
                        }
                    })?
                    .map(|v| v.into_boxed_slice()),
            )
        }
    }

    pub struct MultiProduct<I: Iterator> {
        iters: Box<[I]>,
    }
    impl<I: Iterator> Iterator for MultiProduct<I> {
        type Item = Box<[I::Item]>;

        fn next(&mut self) -> Option<Self::Item> {
            self.iters.iter_mut().map(|i| i.next()).collect()
        }
    }

    pub trait MultiCartesianProduct: Iterator + Sized
    where
        <Self as Iterator>::Item: Iterator + Sized,
    {
        fn multi_product(self) -> MultiProduct<Self::Item> {
            MultiProduct {
                iters: self.collect(),
            }
        }
    }

    impl<I: Iterator + Sized> MultiCartesianProduct for I where
        <Self as Iterator>::Item: Iterator + Sized
    {
    }
}
pub use try_multi_product::{MultiCartesianProduct, MultiProductWithResults, TryMultiProduct};
