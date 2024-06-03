use std::num::{NonZeroU32, NonZeroUsize};

use ff::{Field, PrimeField};
use halo2curves::CurveAffine;
use itertools::Itertools;
use rayon::prelude::*;

use crate::{
    fft,
    plonk::{self, eval, GetChallenges, GetWitness, PlonkStructure},
    polynomial::{lagrange, univariate::UnivariatePoly},
};

use super::pow_i;

#[derive(Debug, thiserror::Error, PartialEq, Eq, Clone)]
pub enum Error {
    #[error(transparent)]
    Eval(#[from] eval::Error),
    #[error(transparent)]
    Pow(#[from] pow_i::Error),
    #[error("pow_i iterator ended before witnesses")]
    PowiEndedBeforeWitnesses,
}

pub(crate) fn compute_F<C: CurveAffine>(
    beta: C::ScalarExt,
    delta: C::ScalarExt,
    S: &PlonkStructure<C::ScalarExt>,
    trace: &(impl Sync + GetChallenges<C::ScalarExt> + GetWitness<C::ScalarExt>),
) -> Result<UnivariatePoly<C::ScalarExt>, Error> {
    struct ZipWitnessWithPowIIterators<F, I, P>
    where
        F: PrimeField,
        I: Iterator<Item = Result<F, eval::Error>>,
        P: Iterator<Item = F>,
    {
        evaluated_witness: I,
        pow_i: Box<[P]>,
    }

    impl<F, I, P> Iterator for ZipWitnessWithPowIIterators<F, I, P>
    where
        F: PrimeField,
        I: Iterator<Item = Result<F, eval::Error>>,
        P: Iterator<Item = F>,
    {
        type Item = Result<Box<[F]>, Error>;

        fn next(&mut self) -> Option<Self::Item> {
            let evaluated_witness = match self.evaluated_witness.next()? {
                Ok(w) => w,
                Err(err) => {
                    return Some(Err(err.into()));
                }
            };

            match self
                .pow_i
                .iter_mut()
                .map(move |p| {
                    p.next()
                        .map(|evaluated_pow_i| evaluated_pow_i * evaluated_witness)
                })
                .collect()
            {
                Some(evaluated) => Some(Ok(evaluated)),
                None => Some(Err(Error::PowiEndedBeforeWitnesses)),
            }
        }
    }

    let count_of_rows = 2usize.pow(S.k as u32);
    let count_of_gates = S.gates.len();

    let n = match NonZeroUsize::new(count_of_rows * count_of_gates) {
        Some(val) => val,
        None => {
            return Ok(UnivariatePoly::new(0));
        }
    };

    let log_n = NonZeroU32::new(n.ilog2()).expect("log2 of non zero element can't be zero");
    let points_count = (log_n.get() + 1) as usize;

    let mut evaluated_points = ZipWitnessWithPowIIterators {
        evaluated_witness: plonk::iter_evaluate_witness::<C>(S, trace),
        pow_i: lagrange::iter_cyclic_subgroup::<C::ScalarExt>(log_n.get())
            .map(|X| beta + X * delta)
            .map(|challenge| pow_i::iter_eval_of_pow_i(log_n, challenge))
            .take(points_count)
            .collect::<Result<Box<[_]>, _>>()?,
    }
    .par_bridge()
    .try_reduce(
        || vec![C::ScalarExt::ZERO; points_count].into_boxed_slice(),
        |mut poly, evaluated_witness_mul_pow_i| {
            poly.iter_mut()
                .zip_eq(evaluated_witness_mul_pow_i.iter())
                .for_each(|(poly, el)| {
                    *poly += el;
                });

            Ok(poly)
        },
    )?;

    fft::ifft(&mut evaluated_points, log_n.get());

    Ok(UnivariatePoly(evaluated_points))
}
