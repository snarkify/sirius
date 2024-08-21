use std::{
    iter,
    ops::{Add, Mul},
};

use halo2_proofs::halo2curves::ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{ff::Field, fft};

/// Represents a univariate polynomial
///
/// Coefficients of the polynomial are presented from smaller to larger
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UnivariatePoly<F: Field>(pub(crate) Box<[F]>);

impl<F: Field> UnivariatePoly<F> {
    pub fn new_zeroed(size: usize) -> Self {
        Self::from_iter(iter::repeat(F::ZERO).take(size))
    }
    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.0.iter()
    }
}

impl<F: Field> IntoIterator for UnivariatePoly<F> {
    type Item = F;
    type IntoIter = <Box<[F]> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        <Box<[F]> as IntoIterator>::into_iter(self.0)
    }
}

impl<F: Field> AsMut<[F]> for UnivariatePoly<F> {
    fn as_mut(&mut self) -> &mut [F] {
        self.0.as_mut()
    }
}

impl<F: Field> FromIterator<F> for UnivariatePoly<F> {
    fn from_iter<T: IntoIterator<Item = F>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<F: Field> UnivariatePoly<F> {
    /// Evaluates the polynomial at a given challenge (point at field)
    pub fn eval(&self, challenge: F) -> F {
        self.0
            .iter()
            .zip(iter::successors(Some(F::ONE), |val| Some(*val * challenge)))
            .fold(F::ZERO, |res, (coeff, challenge_in_degree)| {
                res + (challenge_in_degree * *coeff)
            })
    }

    pub fn resize(self, new_len: usize) -> Self {
        if self.len() == new_len {
            return self;
        }

        let mut coeff = self.0.into_vec();
        coeff.resize(new_len, F::ZERO);
        Self(coeff.into_boxed_slice())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Multiplies all coefficients of the polynomial by a field element.
    pub fn scale(&self, factor: F) -> UnivariatePoly<F> {
        let scaled_coeffs: Vec<F> = self.iter().map(|&coeff| coeff * factor).collect();
        UnivariatePoly(scaled_coeffs.into_boxed_slice())
    }
}

impl<F: Field> Mul<&UnivariatePoly<F>> for UnivariatePoly<F> {
    type Output = UnivariatePoly<F>;

    fn mul(self, rhs: &UnivariatePoly<F>) -> UnivariatePoly<F> {
        let new_len = self.len() + rhs.len() - 1;
        let mut result = vec![F::ZERO; new_len];

        for (i, &a) in self.iter().enumerate() {
            for (j, &b) in rhs.iter().enumerate() {
                result[i + j] += a * b;
            }
        }

        // Skip trailing zeros using itertools
        // Efficiently remove trailing zeros
        let last_non_zero = result
            .iter()
            .rposition(|&x| x != F::ZERO)
            .map_or(0, |pos| pos + 1);

        result.truncate(last_non_zero);

        UnivariatePoly(result.into_boxed_slice())
    }
}

impl<F: Field> Add for UnivariatePoly<F> {
    type Output = UnivariatePoly<F>;

    fn add(self, rhs: UnivariatePoly<F>) -> UnivariatePoly<F> {
        let (longer, shorter) = if self.len() >= rhs.len() {
            (self, rhs)
        } else {
            (rhs, self)
        };

        let mut result = longer.0.into_vec();

        for (res_coeff, &short_coeff) in result.iter_mut().zip(shorter.iter()) {
            *res_coeff += short_coeff;
        }

        // Efficiently remove trailing zeros
        let last_non_zero = result
            .iter()
            .rposition(|&x| x != F::ZERO)
            .map_or(0, |pos| pos + 1);

        result.truncate(last_non_zero);

        UnivariatePoly(result.into_boxed_slice())
    }
}

impl<F: PrimeField> UnivariatePoly<F> {
    pub fn fft(mut self) -> Box<[F]> {
        fft::fft(self.as_mut());
        self.0
    }

    pub fn ifft(mut input: Box<[F]>) -> Self {
        fft::ifft(&mut input);
        Self(input)
    }
}

impl<F: WithSmallOrderMulGroup<3>> UnivariatePoly<F> {
    pub fn coset_fft(mut self) -> Box<[F]> {
        fft::coset_fft(self.as_mut());
        self.0
    }

    pub fn coset_ifft(mut input: Box<[F]>) -> Self {
        fft::coset_ifft(&mut input);
        Self(input)
    }
}

#[cfg(test)]
mod tests {
    use std::iter;

    use super::UnivariatePoly;
    use crate::halo2curves::bn256::Fr;

    // Helper to create an `Fr` iterator from a `u64` iterator
    trait ToF<I: Into<Fr>>: Sized + IntoIterator<Item = I> {
        fn to_f(self) -> impl IntoIterator<Item = Fr> {
            self.into_iter().map(|v| v.into())
        }
    }
    impl<I: Into<Fr>, ITER: Sized + IntoIterator<Item = I>> ToF<I> for ITER {}

    #[test]
    fn test_constant_polynomial() {
        assert_eq!(
            UnivariatePoly::from_iter([5].to_f()).eval(10.into()),
            5.into(),
            "Constant polynomial evaluation failed."
        );
    }

    #[test]
    fn test_linear_polynomial() {
        assert_eq!(
            UnivariatePoly::from_iter([3, 2].to_f()).eval(4.into()),
            11.into(),
            "Linear polynomial evaluation failed."
        );
    }

    #[test]
    fn test_quadratic_polynomial() {
        assert_eq!(
            UnivariatePoly::from_iter([3, 2, 1].to_f()).eval(2.into()),
            11.into(),
            "Quadratic polynomial evaluation failed."
        );
    }

    #[test]
    fn test_high_degree_polynomial() {
        let coeff = [5, 1, 2, 3, 4];
        let point = 2.into();

        let points = iter::successors(Some(1), |acc| Some(acc * 2))
            .take(5)
            .collect::<Vec<_>>();
        let expected = coeff[0] * points[0]
            + coeff[1] * points[1]
            + coeff[2] * points[2]
            + coeff[3] * points[3]
            + coeff[4] * points[4];

        assert_eq!(
            UnivariatePoly::from_iter(coeff.to_f()).eval(point),
            expected.into(),
            "High-degree polynomial evaluation failed."
        );
    }

    #[test]
    fn test_zero_polynomial() {
        assert_eq!(
            UnivariatePoly::<Fr>::from_iter(iter::empty()).eval(1.into()),
            Fr::zero(),
            "Zero polynomial evaluation failed."
        );
    }
}
