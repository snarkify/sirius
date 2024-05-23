use crate::util;
use ff::{Field, PrimeField};
use group::{GroupOpsOwned, ScalarMulOwned};
pub use halo2curves::{CurveAffine, CurveExt};

/// Given FFT domain size k, return the omega in case of fft
/// or return the omega_inv in case if ifft
/// TODO: can consider hardcode if this fn is called multiple times
pub(crate) fn get_omega_or_inv<F: PrimeField>(k: u32, is_inverse: bool) -> F {
    assert!(k <= F::S, "k={} should no larger than F::S={}", k, F::S);
    let mut omega_or_inv = if is_inverse {
        F::ROOT_OF_UNITY_INV
    } else {
        F::ROOT_OF_UNITY
    };
    for _ in k..F::S {
        omega_or_inv = omega_or_inv.square();
    }
    omega_or_inv
}

pub(crate) fn get_ifft_divisor<F: PrimeField>(k: u32) -> F {
    F::TWO_INV.pow_vartime([k as u64])
}

/// This represents an element of a group with basic operations that can be
/// performed. This allows an FFT implementation (for example) to operate
/// generically over either a field or elliptic curve group.
pub trait FftGroup<Scalar: Field>: Copy + Send + GroupOpsOwned + ScalarMulOwned<Scalar> {}

impl<T, Scalar> FftGroup<Scalar> for T
where
    Scalar: Field,
    T: Copy + Send + GroupOpsOwned + ScalarMulOwned<Scalar>,
{
}

/// Performs a radix-$2$ Fast-Fourier Transformation (FFT) on a vector of size
/// $n = 2^k$, when provided `log_n` = $k$ and an element of multiplicative
/// order $n$ called `omega` ($\omega$). The result is that the vector `a`, when
/// interpreted as the coefficients of a polynomial of degree $n - 1$, is
/// transformed into the evaluations of this polynomial at each of the $n$
/// distinct powers of $\omega$. This transformation is invertible by providing
/// $\omega^{-1}$ in place of $\omega$ and dividing each resulting field element
/// by $n$.
///
/// This will use multithreading if beneficial.
pub(crate) fn best_fft<Scalar: Field, G: FftGroup<Scalar>>(a: &mut [G], omega: Scalar, log_n: u32) {
    fn bitreverse(input: usize, limit: usize) -> usize {
        assert!(
            limit <= usize::BITS as usize,
            "Bit length exceeds `usize` capacity"
        );

        let mask = (1 << limit) - 1;
        input.reverse_bits() >> (usize::BITS as usize - limit) & mask
    }

    let threads = rayon::current_num_threads();
    let log_threads = threads.ilog2();
    let n = a.len();
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n as usize);
        if k < rk {
            a.swap(rk, k);
        }
    }

    // precompute twiddle factors
    let twiddles: Vec<_> = (0..(n / 2))
        .scan(Scalar::ONE, |w, _| {
            let tw = *w;
            *w *= &omega;
            Some(tw)
        })
        .collect();

    if log_n <= log_threads {
        let mut chunk = 2_usize;
        let mut twiddle_chunk = n / 2;
        for _ in 0..log_n {
            a.chunks_mut(chunk).for_each(|coeffs| {
                let (left, right) = coeffs.split_at_mut(chunk / 2);

                // case when twiddle factor is one
                let (a, left) = left.split_at_mut(1);
                let (b, right) = right.split_at_mut(1);
                let t = b[0];
                b[0] = a[0];
                a[0] += &t;
                b[0] -= &t;

                left.iter_mut()
                    .zip(right.iter_mut())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let mut t = *b;
                        t *= &twiddles[(i + 1) * twiddle_chunk];
                        *b = *a;
                        *a += &t;
                        *b -= &t;
                    });
            });
            chunk *= 2;
            twiddle_chunk /= 2;
        }
    } else {
        recursive_butterfly_arithmetic(a, n, 1, &twiddles)
    }
}

/// This perform recursive butterfly arithmetic
pub(crate) fn recursive_butterfly_arithmetic<Scalar: Field, G: FftGroup<Scalar>>(
    a: &mut [G],
    n: usize,
    twiddle_chunk: usize,
    twiddles: &[Scalar],
) {
    if n == 2 {
        let t = a[1];
        a[1] = a[0];
        a[0] += &t;
        a[1] -= &t;
    } else {
        let (left, right) = a.split_at_mut(n / 2);
        rayon::join(
            || recursive_butterfly_arithmetic(left, n / 2, twiddle_chunk * 2, twiddles),
            || recursive_butterfly_arithmetic(right, n / 2, twiddle_chunk * 2, twiddles),
        );

        // case when twiddle factor is one
        let (a, left) = left.split_at_mut(1);
        let (b, right) = right.split_at_mut(1);
        let t = b[0];
        b[0] = a[0];
        a[0] += &t;
        b[0] -= &t;

        left.iter_mut()
            .zip(right.iter_mut())
            .enumerate()
            .for_each(|(i, (a, b))| {
                let mut t = *b;
                t *= &twiddles[(i + 1) * twiddle_chunk];
                *b = *a;
                *a += &t;
                *b -= &t;
            });
    }
}

/// fft with input size 1 << log_n
/// This is a wrapper around fn best_fft
pub fn fft<F: PrimeField>(a: &mut [F], log_n: u32) {
    best_fft(a, get_omega_or_inv(log_n, false), log_n);
}

/// inverse fft with input size 1 << log_n
pub fn ifft<F: PrimeField>(a: &mut [F], log_n: u32) {
    let omega_inv = get_omega_or_inv(log_n, true);
    let divisor = get_ifft_divisor(log_n);
    best_fft(a, omega_inv, log_n);
    util::parallelize(a, |(a, _)| {
        for a in a {
            *a *= &divisor;
        }
    });
}

#[cfg(test)]
mod tests {
    use std::array;

    use super::*;
    use halo2curves::bn256::Fr;
    use itertools::Itertools;
    use rand_core::OsRng;

    #[test]
    fn fft_simple_input_test() {
        let test_vector = [
            Fr::from_str_vartime("28").unwrap(),
            Fr::from_str_vartime(
                "68918385373930674424918168212551896122229959265833979749191472831399925654",
            )
            .unwrap(),
            Fr::from_str_vartime("17631683881184975370165255887551781615748388533673675138856")
                .unwrap(),
            Fr::from_str_vartime(
                "68918385373930639161550405842601155791718184162270748252414405484049647934",
            )
            .unwrap(),
            Fr::from_str_vartime(
                "21888242871839275222246405745257275088548364400416034343698204186575808495613",
            )
            .unwrap(),
            Fr::from_str_vartime(
                "21819324486465344583084855339414673932756646216253763595445789781091758847675",
            )
            .unwrap(),
            Fr::from_str_vartime(
                "21888242871839275204614721864072299718383108512864252727949815652902133356753",
            )
            .unwrap(),
            Fr::from_str_vartime(
                "21819324486465344547821487577044723192426134441150200363949012713744408569955",
            )
            .unwrap(),
        ];

        let mut a: [Fr; 8] = array::from_fn(|idx| Fr::from_u128(idx as u128));
        fft(&mut a, 3);

        a.iter().zip_eq(test_vector.iter()).for_each(|(lhs, rhs)| {
            assert_eq!(*lhs, *rhs);
        });
    }

    fn generate_random_input<F: PrimeField>(k: u32) -> Vec<F> {
        let n = 1 << k;
        vec![F::random(OsRng); n]
    }

    #[test]
    fn fft_random_input_test() {
        for k in [4, 5, 6, 7, 8] {
            let input: Vec<Fr> = generate_random_input(k);
            let mut a: Vec<Fr> = input.clone();

            fft(&mut a, k);

            ifft(&mut a, k);

            a.into_iter().zip_eq(input).for_each(|(ai, bi)| {
                assert_eq!(ai, bi);
            });
        }
    }
}
