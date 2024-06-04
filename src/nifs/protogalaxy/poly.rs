use std::num::{NonZeroU32, NonZeroUsize};

use ff::{Field, PrimeField};
use halo2curves::CurveAffine;
use itertools::Itertools;
use rayon::prelude::*;
use tracing::*;

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

#[instrument(skip_all)]
pub(crate) fn compute_F<C: CurveAffine>(
    beta: C::ScalarExt,
    delta: C::ScalarExt,
    S: &PlonkStructure<C::ScalarExt>,
    trace: &(impl Sync + GetChallenges<C::ScalarExt> + GetWitness<C::ScalarExt>),
) -> Result<UnivariatePoly<C::ScalarExt>, Error> {
    struct MultiProduct<F, I, P>
    where
        F: PrimeField,
        I: Iterator<Item = Result<F, eval::Error>>,
        P: Iterator<Item = F>,
    {
        evaluated_witness: I,
        iters_with_pow_i: Box<[P]>,
    }

    impl<F, I, P> Iterator for MultiProduct<F, I, P>
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
                .iters_with_pow_i
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

    let count_of_evaluation = match NonZeroUsize::new(count_of_rows * count_of_gates) {
        Some(val) => val,
        None => {
            return Ok(UnivariatePoly::new(0));
        }
    };

    let log_n = NonZeroU32::new(count_of_evaluation.get().ilog2()).unwrap();

    let points_count = count_of_evaluation
        .get()
        .next_power_of_two()
        .ilog2()
        .next_power_of_two() as usize;

    debug!(
        "
        count_of_rows: {count_of_rows};
        count_of_gates: {count_of_gates};
        count_of_evaluation: {count_of_evaluation};
        log_n: {log_n};
        points_count: {points_count}"
    );

    use itertools::*;
    let iters_with_pow_i = lagrange::iter_cyclic_subgroup::<C::ScalarExt>(log_n.get())
        .map(|X| beta + X * delta)
        .map(|challenge| pow_i::iter_eval_of_pow_i(log_n, count_of_evaluation, challenge))
        .take(points_count)
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .multi_cartesian_product();

    let mut evaluated_points = MultiProduct {
        evaluated_witness: plonk::iter_evaluate_witness::<C>(S, trace),
        iters_with_pow_i: lagrange::iter_cyclic_subgroup::<C::ScalarExt>(log_n.get())
            .map(|X| beta + X * delta)
            .map(|challenge| pow_i::iter_eval_of_pow_i(log_n, count_of_evaluation, challenge))
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

    fft::ifft(&mut evaluated_points, points_count.ilog2());

    Ok(UnivariatePoly(evaluated_points))
}

#[cfg(test)]
mod test {
    use crate::plonk::test_eval_witness::poseidon_circuit;

    use ff::Field as _Field;
    use halo2curves::{bn256, CurveAffine};
    use tracing_test::traced_test;

    use crate::{
        commitment::CommitmentKey,
        plonk::PlonkTrace,
        poseidon::{
            random_oracle::{self, ROTrait},
            PoseidonRO, Spec,
        },
        table::CircuitRunner,
    };

    type Curve = bn256::G1Affine;
    type Field = <Curve as CurveAffine>::ScalarExt;

    /// Spec for off-circuit poseidon
    const POSEIDON_PERMUTATION_WIDTH: usize = 3;
    const POSEIDON_RATE: usize = POSEIDON_PERMUTATION_WIDTH - 1;

    const R_F1: usize = 4;
    const R_P1: usize = 3;
    pub type PoseidonSpec =
        Spec<<Curve as halo2curves::CurveAffine>::Base, POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE>;

    type RO = <PoseidonRO<POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE> as random_oracle::ROPair<
        <Curve as halo2curves::CurveAffine>::Base,
    >>::OffCircuit;

    #[traced_test]
    #[test]
    fn test_compute_f() {
        let runner = CircuitRunner::<Field, _>::new(
            12,
            poseidon_circuit::TestPoseidonCircuit::default(),
            vec![],
        );

        let S = runner.try_collect_plonk_structure().unwrap();

        let witness = runner.try_collect_witness().unwrap();

        let (u, w) = S
            .run_sps_protocol(
                &CommitmentKey::<Curve>::setup(15, b"k"),
                &[],
                &witness,
                &mut RO::new(PoseidonSpec::new(R_F1, R_P1)),
                S.num_challenges,
            )
            .unwrap();

        let mut rnd = rand::thread_rng();
        super::compute_F::<Curve>(
            Field::random(&mut rnd),
            Field::random(&mut rnd),
            &S,
            &PlonkTrace { u, w },
        )
        .unwrap();
    }
}
