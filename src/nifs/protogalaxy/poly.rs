use std::num::NonZeroU32;

use ff::Field;
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
    #[error("pow_i iterator ended before witnesses")]
    PowiEndedBeforeWitnesses,
}

/// Analog of [`itertools::structs::MultiProduct`], but:
/// - without [`Clone`] require
/// - without logic for diff len of iterators
struct MultiProduct<Item, Iter>
where
    Iter: Iterator<Item = Item>,
{
    iterators: Box<[Iter]>,
}

impl<Item, Iter> Iterator for MultiProduct<Item, Iter>
where
    Iter: Iterator<Item = Item>,
{
    type Item = Box<[Item]>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterators.iter_mut().map(|p| p.next()).collect()
    }
}

#[instrument(skip_all)]
pub(crate) fn compute_F<C: CurveAffine>(
    beta: C::ScalarExt,
    delta: C::ScalarExt,
    S: &PlonkStructure<C::ScalarExt>,
    trace: &(impl Sync + GetChallenges<C::ScalarExt> + GetWitness<C::ScalarExt>),
) -> Result<UnivariatePoly<C::ScalarExt>, Error> {
    let count_of_rows = 2usize.pow(S.k as u32);
    let count_of_gates = S.gates.len();

    let count_of_evaluation = count_of_rows * count_of_gates;

    let points_count = count_of_evaluation
        .next_power_of_two()
        .ilog2()
        .next_power_of_two() as usize;

    let log_n = NonZeroU32::new(points_count.ilog2()).unwrap();

    debug!(
        "
        count_of_rows: {count_of_rows};
        count_of_gates: {count_of_gates};
        count_of_evaluation: {count_of_evaluation};
        log_n: {log_n};
        points_count: {points_count}"
    );

    let mut evaluated_points = MultiProduct {
        iterators: lagrange::iter_cyclic_subgroup::<C::ScalarExt>(log_n.get())
            .map(|X| pow_i::iter_eval_of_pow_i(log_n, beta + X * delta))
            .take(points_count)
            .collect::<Box<[_]>>(),
    }
    .zip(plonk::iter_evaluate_witness::<C>(S, trace))
    .map(
        |(mut evaluated_pow_i_per_challenge, result_with_evaluated_w_i)| {
            let evaluated_w_i = result_with_evaluated_w_i?;

            evaluated_pow_i_per_challenge
                .iter_mut()
                .for_each(|evaluated_pow_i| {
                    *evaluated_pow_i *= evaluated_w_i;
                });

            Result::<_, Error>::Ok(evaluated_pow_i_per_challenge)
        },
    )
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
