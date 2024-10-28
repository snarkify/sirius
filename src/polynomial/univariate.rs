use std::{
    cmp::Ordering,
    iter,
    ops::{Add, Mul},
};

use halo2_proofs::halo2curves::ff::{PrimeField, WithSmallOrderMulGroup};

use crate::{ff::Field, fft, util};

/// Represents a univariate polynomial
///
/// Coefficients of the polynomial are presented from smaller degree to larger degree
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UnivariatePoly<F: Field>(pub(crate) Box<[F]>);

impl<F: Field> UnivariatePoly<F> {
    pub fn new_zeroed(size: usize) -> Self {
        Self::from_iter(iter::repeat(F::ZERO).take(size))
    }
    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.0.iter()
    }
    pub fn degree(&self) -> usize {
        self.0
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, coeff)| F::ZERO.ne(coeff).then_some(i))
            .unwrap_or_default()
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

    pub fn pad_with_zeroes(self, new_len: usize) -> Result<Self, Self> {
        match self.len().cmp(&new_len) {
            Ordering::Equal => Ok(self),
            Ordering::Less => {
                let mut coeff = self.0.into_vec();
                coeff.resize(new_len, F::ZERO);
                Ok(Self(coeff.into_boxed_slice()))
            }
            Ordering::Greater => Err(self),
        }
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

    pub fn fe_to_fe<F2: PrimeField>(&self) -> Option<UnivariatePoly<F2>> {
        self.0
            .iter()
            .map(|coeff| util::fe_to_fe(coeff))
            .collect::<Option<Box<[_]>>>()
            .map(UnivariatePoly)
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

    #[test]
    fn test_degree_zero_polynomial() {
        let poly = UnivariatePoly::from_iter([Fr::from(5)]);
        assert_eq!(poly.degree(), 0, "Degree of a zero polynomial failed.");

        let poly = UnivariatePoly::from_iter([Fr::from(0)]);
        assert_eq!(poly.degree(), 0, "Degree of a zero polynomial failed.");
    }

    #[test]
    fn test_degree_nonzero_polynomial() {
        let poly = UnivariatePoly::from_iter([Fr::from(3), Fr::from(0), Fr::from(7)]);
        assert_eq!(poly.degree(), 2, "Degree of a nonzero polynomial failed.");
    }

    #[test]
    fn test_degree_zero_start() {
        let poly = UnivariatePoly::from_iter([Fr::from(3), Fr::from(0), Fr::from(0)]);
        assert_eq!(poly.degree(), 0, "Degree of a nonzero polynomial failed.");
    }

    #[test]
    fn test_add_polynomials() {
        let poly1 = UnivariatePoly::from_iter([Fr::from(3), Fr::from(2), Fr::from(1)]);
        let poly2 = UnivariatePoly::from_iter([Fr::from(1), Fr::from(3), Fr::from(2)]);
        let expected_sum = UnivariatePoly::from_iter([Fr::from(4), Fr::from(5), Fr::from(3)]);

        assert_eq!(
            poly1.clone() + poly2.clone(),
            expected_sum,
            "Adding polynomials failed."
        );
    }

    #[test]
    fn test_multiply_polynomials() {
        let poly1 = UnivariatePoly::from_iter([Fr::from(1), Fr::from(2)]);
        let poly2 = UnivariatePoly::from_iter([Fr::from(1), Fr::from(2)]);
        let expected_product = UnivariatePoly::from_iter([Fr::from(1), Fr::from(4), Fr::from(4)]);

        assert_eq!(
            poly1.clone() * &poly2.clone(),
            expected_product,
            "Multiplying polynomials failed."
        );
    }

    #[test]
    fn test_resize_polynomial_larger() {
        let poly = UnivariatePoly::from_iter((0..3).map(Fr::from));

        assert_eq!(
            poly.clone().pad_with_zeroes(5),
            Ok(UnivariatePoly::from_iter([0, 1, 2, 0, 0].map(Fr::from))),
            "Resizing polynomial to a larger size failed."
        );
    }

    #[test]
    fn test_resize_polynomial_smaller() {
        let poly = UnivariatePoly::from_iter((0..5).map(Fr::from));
        let expected = poly.clone();

        assert_eq!(
            poly.pad_with_zeroes(3),
            Err(expected),
            "Resizing polynomial to a smaller size failed."
        );
    }

    #[test]
    fn test_resize_polynomial_same_size() {
        let poly = UnivariatePoly::from_iter((0..3).map(Fr::from));
        let resized = poly.clone().pad_with_zeroes(3);

        assert_eq!(
            resized,
            Ok(poly),
            "Resizing polynomial to the same size failed."
        );
    }

    #[test]
    fn test_scale_polynomial() {
        let poly = UnivariatePoly::from_iter((0..3).map(Fr::from)); // Polynomial: 0 + 1*x + 2*x^2
        let factor = Fr::from(2);
        let scaled = poly.scale(factor);
        let expected = UnivariatePoly::from_iter((0..3).map(|x| Fr::from(x) * factor)); // Polynomial: 0 + 2*x + 4*x^2
        assert_eq!(scaled, expected, "Scaling polynomial failed.");
    }
}
