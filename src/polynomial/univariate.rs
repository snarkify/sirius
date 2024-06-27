use std::iter;

use ff::Field;
use halo2_proofs::halo2curves::ff;

/// Represents a univariate polynomial
///
/// Coefficients of the polynomial are presented from smaller to larger
#[derive(Debug, PartialEq, Eq)]
pub struct UnivariatePoly<F: Field>(pub(crate) Box<[F]>);

impl<F: Field> UnivariatePoly<F> {
    pub fn new_zeroed(size: usize) -> Self {
        Self::from_iter(iter::repeat(F::ZERO).take(size))
    }
    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.0.iter()
    }
}

impl<F: Field> FromIterator<F> for UnivariatePoly<F> {
    fn from_iter<T: IntoIterator<Item = F>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<F: Field> UnivariatePoly<F> {
    /// Evaluates the polynomial at a given challenge (point at field)
    pub fn eval(self, challenge: F) -> F {
        self.0
            .iter()
            .zip(iter::successors(Some(F::ONE), |val| Some(*val * challenge)))
            .fold(F::ZERO, |res, (coeff, challenge_in_degree)| {
                res + (challenge_in_degree * *coeff)
            })
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
