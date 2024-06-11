use std::{
    iter,
    num::{NonZeroU32, NonZeroUsize},
};

use ff::{Field, PrimeField};
use halo2curves::CurveAffine;
use itertools::*;
use num_traits::Zero;
use rayon::prelude::*;
use tracing::*;

use crate::{
    fft,
    plonk::{self, eval, GetChallenges, GetWitness, PlonkStructure, PlonkWitness},
    polynomial::{expression::QueryIndexContext, lagrange, univariate::UnivariatePoly},
    util::TryMultiProduct,
};

#[derive(Debug, thiserror::Error, PartialEq, Eq, Clone)]
pub enum Error {
    #[error(transparent)]
    Eval(#[from] eval::Error),
    #[error("You can't fold 0 traces")]
    EmptyTracesNotAllowed,
}

/// This function calculates F(X), which mathematically looks like this:
///
/// $$F(X)=\sum_{i=0}^{n-1}pow_{i}(\boldsymbol{\beta}+X\cdot\boldsymbol{\delta})f_i(w)$$
///
/// - `f_i` - iteratively all gates for all rows sequentially. The order is taken from
///           [`plonk::iter_evaluate_witness`].
/// - `pow_i` - `i` degree of challenge
///
/// # Algorithm
///
/// We use [`Itertools::tree_reduce`] & create `points_count` iterators for `pow_i`, where each
/// iterator uses a different challenge (`X`) from the cyclic group, and then iterate over all
/// these iterators at once.
///
/// I.e. item `i` from this iterator is a collection of [pow_i(X0), pow_i(X1), ...]
///
/// f₀  f₁ f₂  f₃  f₄  f₅  f₆  f₇
/// │   │  │   │   │   │   │   │
/// 1   β  1   β   1   β   1   β
/// │   │  │   │   │   │   │   │
/// └───f₀₁└───f₂₃ └───f₄₅ └───f₆₇
///     │      │       │       │
///     1      β²      1       β²
///     │      │       │       │
///     └──────f₀₁₂₃   └───────f₄₅₆₇
///            │               │
///            └───────────────f₀₁₂₃₄₅₆₇
///
/// Each β here is a vector of all `X`, and each node except leaves contains all counted
/// Each `f` here is fₙₘ =  fₙ * 1 + fₘ * βⁱ
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

    if count_of_evaluation == 0 {
        return Ok(UnivariatePoly::new_zeroed(0));
    }

    let points_count = count_of_evaluation
        .next_power_of_two()
        .ilog2()
        .next_power_of_two() as usize;

    let fft_domain_size = NonZeroU32::new(points_count.ilog2()).unwrap();

    debug!(
        "
        count_of_rows: {count_of_rows};
        count_of_gates: {count_of_gates};
        count_of_evaluation: {count_of_evaluation};
        fft_domain_size: {fft_domain_size};
        points_count: {points_count}"
    );

    // Use the elements of the cyclic group together with beta & delta as challenge and calculate them
    // degrees
    //
    // Since we are using a tree-based algorithm, we need `{X^1, X^2, ..., X^{log2(n)}}` of all
    // challenges.
    //
    // Even for large `count_of_evaluation` this will be a small number, so we can
    // collect it
    let challenges_powers = lagrange::iter_cyclic_subgroup::<C::ScalarExt>(fft_domain_size.get())
        .map(|X| {
            iter::successors(Some(beta + X * delta), |ch| Some(ch.double()))
                .take(count_of_evaluation.next_power_of_two().ilog2() as usize)
                .collect::<Box<_>>()
        })
        .take(points_count)
        .collect::<Box<[_]>>();

    /// Auxiliary wrapper for using the tree to evaluate polynomials
    #[derive(Debug)]
    enum Node<F: PrimeField> {
        Leaf(F),
        Calculated {
            /// Intermediate results for all calculated challenges
            /// Every point calculated for specific challenge
            points: Box<[F]>,
            /// Node height relative to leaf height
            height: NonZeroUsize,
        },
    }

    let evaluated = plonk::iter_evaluate_witness::<C>(S, trace)
        .map(|result_with_evaluated_gate| result_with_evaluated_gate.map(Node::Leaf))
        // TODO #259 Migrate to a parallel algorithm
        // TODO #259 Implement `try_tree_reduce` to stop on the first error
        .tree_reduce(|left_w, right_w| {
            let (left_w, right_w) = (left_w?, right_w?);

            match (left_w, right_w) {
                (Node::Leaf(left), Node::Leaf(right)) => Ok(Node::Calculated {
                    points: challenges_powers
                        .iter()
                        .map(|challenge_powers| left + (right * challenge_powers[0]))
                        .collect(),
                    height: NonZeroUsize::new(1).unwrap(),
                }),
                (
                    Node::Calculated {
                        points: mut left,
                        height: l_height,
                    },
                    Node::Calculated {
                        points: right,
                        height: r_height,
                    },
                    // The tree must be binary, so we only calculate at the one node level
                ) if l_height.eq(&r_height) => {
                    itertools::multizip((challenges_powers.iter(), left.iter_mut(), right.iter()))
                        .for_each(|(challenge_powers, left, right)| {
                            *left += *right * challenge_powers[l_height.get()]
                        });

                    Ok(Node::Calculated {
                        points: left,
                        height: l_height.saturating_add(1),
                    })
                }
                other => unreachable!("this case must be unreachable: {other:?}"),
            }
        });

    match evaluated {
        Some(Ok(Node::Calculated { mut points, .. })) => {
            fft::ifft(&mut points, fft_domain_size.get());
            Ok(UnivariatePoly(points))
        }
        Some(Err(err)) => Err(err.into()),
        other => unreachable!("this case must be unreachable: {other:?}"),
    }
}

struct FoldedTrace<F: PrimeField> {
    witness: PlonkWitness<F>,
    challenges: Vec<F>,
}

impl<F: PrimeField> FoldedTrace<F> {
    fn new(
        points_for_fft: &[F],
        fft_domain_size: u32,
        accumulator: impl Sync + GetChallenges<F> + GetWitness<F>,
        traces: &[(impl Sync + GetChallenges<F> + GetWitness<F>)],
    ) -> Box<[Self]> {
        let folded_witnesses_collection = fold_witnesses(points_for_fft, &accumulator, traces);
        let folded_challenges_collection =
            fold_plonk_challenges(points_for_fft, fft_domain_size, &accumulator, traces);

        folded_witnesses_collection
            .into_iter()
            .zip(folded_challenges_collection)
            .map(|(witness, challenges)| Self {
                witness,
                challenges,
            })
            .collect()
    }
}
impl<F: PrimeField> GetChallenges<F> for FoldedTrace<F> {
    fn get_challenges(&self) -> &[F] {
        &self.challenges
    }
}
impl<F: PrimeField> GetWitness<F> for FoldedTrace<F> {
    fn get_witness(&self) -> &[Vec<F>] {
        &self.witness.W
    }
}

pub(crate) fn compute_G<C: CurveAffine>(
    beta_stroke: C::ScalarExt,
    S: &PlonkStructure<C::ScalarExt>,
    accumulator: impl Sync + GetChallenges<C::ScalarExt> + GetWitness<C::ScalarExt>,
    traces: &[(impl Sync + GetChallenges<C::ScalarExt> + GetWitness<C::ScalarExt>)],
) -> Result<UnivariatePoly<C::ScalarExt>, Error> {
    let ctx = QueryIndexContext::from(S);
    let max_degree = S
        .gates
        .iter()
        .map(|poly| poly.degree(&ctx))
        .max()
        .unwrap_or_default();

    if traces.is_empty() {
        return Err(Error::EmptyTracesNotAllowed);
    }

    // `1` from accumulator
    let count_of_folding_traces = 1 + traces.len();

    let count_of_rows = 2usize.pow(S.k as u32);
    let count_of_gates = S.gates.len();

    let count_of_evaluation = count_of_rows * count_of_gates;
    if count_of_evaluation.is_zero() {
        return Ok(UnivariatePoly::new_zeroed(0));
    }

    let points_count = (count_of_folding_traces * max_degree + 1).next_power_of_two();
    let fft_domain_size = points_count.ilog2();

    let powers_of_beta_stroke = iter::successors(Some(beta_stroke), |ch| Some(ch.double()))
        .take(count_of_evaluation.next_power_of_two().ilog2() as usize)
        .collect::<Box<[C::ScalarExt]>>();

    let points_for_fft = lagrange::iter_cyclic_subgroup(fft_domain_size)
        .take(points_count)
        .collect::<Box<[_]>>();

    /// Auxiliary wrapper for using the tree to evaluate polynomials
    #[derive(Debug)]
    enum Node<F: PrimeField> {
        Leaf(Box<[F]>),
        Calculated {
            /// Intermediate results for all calculated points
            ///
            /// Every point calculated for specific challenge
            points: Box<[F]>,
            /// Node height relative to leaf height
            height: NonZeroUsize,
        },
    }

    let evaluated = FoldedTrace::new(&points_for_fft, fft_domain_size, accumulator, traces)
        .iter()
        .map(|folded_trace| plonk::iter_evaluate_witness::<C>(S, folded_trace))
        .try_multi_product()
        .map(|points| points.map(Node::Leaf))
        .tree_reduce(|left, right| {
            let (left, right) = (left?, right?);

            match (left, right) {
                (Node::Leaf(mut left), Node::Leaf(right)) => {
                    left.iter_mut().zip(right.iter()).for_each(|(left, right)| {
                        *left += *right * powers_of_beta_stroke[0];
                    });

                    Ok(Node::Calculated {
                        points: left,
                        height: NonZeroUsize::new(1).unwrap(),
                    })
                }
                (
                    Node::Calculated {
                        points: mut left,
                        height: l_height,
                    },
                    Node::Calculated {
                        points: right,
                        height: r_height,
                    },
                    // The tree must be binary, so we only calculate at the one node level
                ) if l_height.eq(&r_height) => {
                    left.iter_mut().zip(right.iter()).for_each(|(left, right)| {
                        *left += *right * powers_of_beta_stroke[l_height.get()];
                    });

                    Ok(Node::Calculated {
                        points: left,
                        height: l_height.saturating_add(1),
                    })
                }
                other => unreachable!("this case must be unreachable: {other:?}"),
            }
        });

    match evaluated {
        Some(Ok(Node::Calculated { mut points, .. })) => {
            fft::ifft(&mut points, fft_domain_size);
            Ok(UnivariatePoly(points))
        }
        Some(Err(err)) => Err(err.into()),
        other => unreachable!("this case must be unreachable: {other:?}"),
    }
}

/// For each `X` we must perform the operation of sum all all matrices [`PlonkWitness`] with
/// coefficients taken from [`lagrange::iter_eval_lagrange_polynomials_for_cyclic_group`]
///
/// Since the number of rows is large, we do this in one pass, counting the points for each
/// challenge at each iteration, and laying them out in separate [`PlonkWitness`] at the end.
fn fold_witnesses<F: PrimeField>(
    X_challenges: &[F],
    accumulator: &(impl GetWitness<F> + Sync),
    witnesses: &[impl Sync + GetWitness<F>],
) -> Vec<PlonkWitness<F>> {
    let log_n = (witnesses.len() + 1).next_power_of_two().ilog2();

    let lagrange_poly_by_challenge = X_challenges
        .iter()
        .map(|X| {
            lagrange::iter_eval_lagrange_polynomials_for_cyclic_group(*X, log_n)
                .collect::<Box<[_]>>()
        })
        .collect::<Box<[_]>>();

    let columns_count = accumulator.get_witness().len();
    let rows_count = accumulator.get_witness()[0].len();

    let mut result_matrix_by_challenge = vec![
        PlonkWitness {
            W: vec![vec![F::ZERO; rows_count]; columns_count],
        };
        X_challenges.len()
    ];

    itertools::iproduct!(0..columns_count, 0..rows_count)
        .map(|(col, row)| {
            iter::once(accumulator.get_witness())
                .chain(witnesses.iter().map(GetWitness::get_witness))
                .zip(
                    lagrange_poly_by_challenge
                        .iter()
                        .map(|m| m.iter().copied())
                        .multi_product(),
                )
                .fold(
                    vec![F::ZERO; X_challenges.len()].into_boxed_slice(),
                    // every element of this collection - one cell for each multiplier
                    |mut cells_by_challenge, (matrix, multiplier)| {
                        cells_by_challenge
                            .iter_mut()
                            .zip(multiplier.iter())
                            .for_each(|(res, cell)| {
                                *res += *cell * matrix[col][row];
                            });

                        cells_by_challenge
                    },
                )
        })
        .zip(
            // Here we take an iterator that on each iteration returns [column][row] elements for
            // each witness for its challenge
            //
            // next -> vec![result[0][col][row], result[1][col][row], ... result[challenges_len][col][row]]
            result_matrix_by_challenge
                .iter_mut()
                .map(|matrix| matrix.W.iter_mut().flat_map(|col| col.iter_mut()))
                .multi_product(),
        )
        .par_bridge()
        .for_each(|(elements, mut results)| {
            results
                .iter_mut()
                .zip(elements.iter())
                .for_each(|(result, cell)| **result = *cell);
        });

    result_matrix_by_challenge
}

fn fold_plonk_challenges<F: PrimeField>(
    _X_challanges: &[F],
    _log_n: u32,
    _accumulator: &(impl GetChallenges<F> + Sync),
    _witnesses: &[impl Sync + GetChallenges<F>],
) -> Vec<Vec<F>> {
    todo!()
}

struct MultiProduct<I: Iterator> {
    iters: Box<[I]>,
}
impl<I: Iterator> Iterator for MultiProduct<I> {
    type Item = Box<[I::Item]>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iters.iter_mut().map(|i| i.next()).collect()
    }
}
trait MultiCartesianProduct: Iterator + Sized
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

#[cfg(test)]
mod test {
    use std::iter;

    use crate::{
        plonk::{test_eval_witness::poseidon_circuit, PlonkStructure},
        polynomial::univariate::UnivariatePoly,
    };

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

    fn poseidon_trace() -> (PlonkStructure<Field>, PlonkTrace<Curve>) {
        let runner = CircuitRunner::<Field, _>::new(
            12,
            poseidon_circuit::TestPoseidonCircuit::default(),
            vec![],
        );

        let S = runner.try_collect_plonk_structure().unwrap();
        let witness = runner.try_collect_witness().unwrap();

        let (u, w) = S
            .run_sps_protocol(
                &CommitmentKey::setup(17, b""),
                &[],
                &witness,
                &mut RO::new(PoseidonSpec::new(R_F1, R_P1)),
                S.num_challenges,
            )
            .unwrap();

        (S, PlonkTrace { u, w })
    }

    #[traced_test]
    #[test]
    fn zero_f() {
        let (S, trace) = poseidon_trace();
        let mut rnd = rand::thread_rng();

        assert!(super::compute_F::<Curve>(
            Field::random(&mut rnd),
            Field::random(&mut rnd),
            &S,
            &trace,
        )
        .unwrap()
        .iter()
        .all(|f| f.is_zero().into()));
    }

    #[traced_test]
    #[test]
    fn non_zero_f() {
        let (S, mut trace) = poseidon_trace();
        let mut rnd = rand::thread_rng();
        trace
            .w
            .W
            .iter_mut()
            .for_each(|row| row.iter_mut().for_each(|el| *el = Field::random(&mut rnd)));

        assert_ne!(
            super::compute_F::<Curve>(Field::random(&mut rnd), Field::random(&mut rnd), &S, &trace,),
            Ok(UnivariatePoly::from_iter(
                iter::repeat(Field::ZERO).take(16)
            ))
        );
    }
}
