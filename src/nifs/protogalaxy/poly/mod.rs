use std::num::{NonZeroU32, NonZeroUsize};

use ff::PrimeField;
use group::ff::WithSmallOrderMulGroup;
use itertools::*;
use num_traits::Zero;
use tracing::*;

use crate::{
    fft::{self, coset_fft, coset_ifft},
    plonk::{self, eval, GetChallenges, GetWitness, PlonkStructure},
    polynomial::{expression::QueryIndexContext, lagrange, univariate::UnivariatePoly},
    util::TryMultiProduct,
};

mod folded_trace;
use folded_trace::FoldedTrace;

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
///            1               β⁴
///            │               │
///            └───────────────f₀₁₂₃₄₅₆₇
///
/// Each β here is a vector of all `X`, and each node except leaves contains all counted
/// Each `f` here is fₙₘ =  fₙ * 1 + fₘ * βⁱ
///
/// # Note
///
/// Unlike [`compute_G`] where `X` challenge affects the nodes of the tree and generates multiple
/// values from them, here multiple values are generated by edges, and they are stored everywhere
/// except leaves.
#[instrument(skip_all)]
pub(crate) fn compute_F<F: PrimeField>(
    betas: impl Iterator<Item = F>,
    delta: F,
    S: &PlonkStructure<F>,
    trace: &(impl Sync + GetChallenges<F> + GetWitness<F>),
) -> Result<UnivariatePoly<F>, Error> {
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
    let betas = betas
        .take(count_of_evaluation.next_power_of_two().ilog2() as usize)
        .collect::<Box<[_]>>();

    let challenges_powers = lagrange::iter_cyclic_subgroup::<F>(fft_domain_size.get())
        .map(|X| {
            betas
                .iter()
                .map(|beta| *beta + X * delta)
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

    let evaluated = plonk::iter_evaluate_witness::<F>(S, trace)
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

/// This function calculates G(X), which mathematically looks like this:
///
/// $$G(X)=\sum_{i=0}^{n-1}\operatorname{pow}_i(\boldsymbol{\beta}+\alpha\cdot\boldsymbol{\delta})f_i(L_0(X)w+\sum_{j\in[k]}L_j(X)w_j)$$
///
/// - `f_i` - iteratively all gates for all rows sequentially. The order is taken from
///           [`plonk::iter_evaluate_witness`].
/// - `pow_i` - `i` degree of challenge
/// - `L` - lagrange poly
///
/// # Algorithm
///
/// We use [`Itertools::tree_reduce`] & store in each node `X` points, for each X challenge
///
/// I.e. item `i` from this iterator is a collection of [pow_i(X0), pow_i(X1), ...]
///
/// f₀  f₁ f₂  f₃  f₄  f₅  f₆  f₇
/// │   │  │   │   │   │   │   │
/// 1   β' 1   β'  1   β'  1   β'
/// │   │  │   │   │   │   │   │
/// └───f₀₁└───f₂₃ └───f₄₅ └───f₆₇
///     │      │       │       │
///     1      β'₂     1       β'₂
///     │      │       │       │
///     └──────f₀₁₂₃   └───────f₄₅₆₇
///            │               │
///            1               β'₄
///            │               │
///            └───────────────f₀₁₂₃₄₅₆₇
///
/// Where β'ᵢ= βⁱ + (α * δⁱ)
/// Each `f` here is vector (leafs too) of elements for each challenge with: fₙₘ =  fₙ * 1 + fₘ * β'ᵢ
///
/// # Note
///
/// Unlike [`compute_F`] where `X` challenge affects the edges of the tree, here the set of values
/// is in the nodes
#[instrument(skip_all)]
pub(crate) fn compute_G<F: PrimeField>(
    S: &PlonkStructure<F>,
    betas_stroke: impl Iterator<Item = F>,
    accumulator: &(impl Sync + GetChallenges<F> + GetWitness<F>),
    traces: &[(impl Sync + GetChallenges<F> + GetWitness<F>)],
) -> Result<UnivariatePoly<F>, Error> {
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

    let count_of_rows = 2usize.pow(S.k as u32);
    let count_of_gates = S.gates.len();

    let count_of_evaluation = count_of_rows * count_of_gates;
    if count_of_evaluation.is_zero() {
        return Ok(UnivariatePoly::new_zeroed(0));
    }

    let points_count = (traces.len() * max_degree + 1).next_power_of_two();
    let fft_domain_size = points_count.ilog2();

    let powers_of_beta_stroke = betas_stroke
        .take(count_of_evaluation.next_power_of_two().ilog2() as usize)
        .collect::<Box<[_]>>();

    let points_for_fft = lagrange::iter_cyclic_subgroup(fft_domain_size)
        .take(points_count)
        .collect::<Box<[_]>>();

    /// Auxiliary wrapper for using the tree to evaluate polynomials
    #[derive(Debug)]
    struct Node<F: PrimeField> {
        values: Box<[F]>,
        height: usize,
    }

    let evaluated = FoldedTrace::new(&points_for_fft, accumulator, traces)
        .iter()
        .map(|folded_trace| plonk::iter_evaluate_witness::<F>(S, folded_trace))
        .try_multi_product()
        .map(|points| points.map(|points| Node { values: points, height: 0 }))
        .tree_reduce(|left, right| {
            let (
                Node {
                    values: mut left,
                    height: l_height,
                },
                Node {
                    values: right,
                    height: r_height,
                },
            ) = (left?, right?);

            if l_height.eq(&r_height) {
                left.iter_mut().zip(right.iter()).for_each(|(left, right)| {
                    *left += *right * powers_of_beta_stroke[l_height];
                });

                Ok(Node {
                    values: left,
                    height: l_height.saturating_add(1),
                })
            } else {
                unreachable!("different heights should not be here because the tree is binary: {l_height} != {r_height}")
            }
        });

    match evaluated {
        Some(Ok(Node {
            values: mut points, ..
        })) => {
            fft::ifft(&mut points, fft_domain_size);
            Ok(UnivariatePoly(points))
        }
        Some(Err(err)) => Err(err.into()),
        other => unreachable!("this case must be unreachable: {other:?}"),
    }
}

#[derive(Clone)]
pub(crate) struct PolyChallenges<F: PrimeField> {
    pub(crate) betas: Box<[F]>,
    pub(crate) alpha: F,
    pub(crate) delta: F,
}

pub(crate) struct BetaStrokeIter<F: PrimeField> {
    cha: PolyChallenges<F>,
    beta_index: usize,
}

impl<F: PrimeField> PolyChallenges<F> {
    pub(crate) fn iter_beta_stroke(self) -> BetaStrokeIter<F> {
        BetaStrokeIter {
            cha: self,
            beta_index: 0,
        }
    }
}

impl<F: PrimeField> Iterator for BetaStrokeIter<F> {
    type Item = F;

    fn next(&mut self) -> Option<Self::Item> {
        let next =
            self.cha.betas.get(self.beta_index).copied()? + (self.cha.alpha * self.cha.delta);

        self.beta_index += 1;
        self.cha.delta = self.cha.delta.double();

        Some(next)
    }
}

pub(crate) fn compute_K<F: WithSmallOrderMulGroup<3>>(
    S: &PlonkStructure<F>,
    f_alpha: F,
    betas_stroke: impl Iterator<Item = F>,
    accumulator: &(impl Sync + GetChallenges<F> + GetWitness<F>),
    traces: &[(impl Sync + GetChallenges<F> + GetWitness<F>)],
) -> Result<UnivariatePoly<F>, Error> {
    let mut g_poly = compute_G(S, betas_stroke, accumulator, traces)?;
    // is coeffs here, will transform to evals by fft later
    let ctx = QueryIndexContext::from(S);

    let max_degree = S
        .gates
        .iter()
        .map(|poly| poly.degree(&ctx))
        .max()
        .unwrap_or_default();

    let points_count = (traces.len() * max_degree + 1).next_power_of_two();
    let log_n = points_count.ilog2();

    coset_fft(g_poly.as_mut());

    let mut k_evals = lagrange::iter_eval_lagrange_poly_for_cyclic_group_for_challenges(
        lagrange::iter_cyclic_subgroup::<F>(log_n).map(|pt| F::ZETA * pt),
        log_n,
    )
    .zip(g_poly.iter())
    .map(|((challenge, evaluated_lagrange), g_y)| {
        let l_y = f_alpha * evaluated_lagrange;
        let z_y = lagrange::eval_vanish_polynomial(log_n, challenge);

        // when z_y is on coset domain, invert is save
        (*g_y - l_y) * z_y.invert().unwrap()
    })
    .take(points_count)
    .collect::<Box<[_]>>();

    coset_ifft(k_evals.as_mut());

    Ok(UnivariatePoly(k_evals))
}

#[cfg(test)]
mod test {
    use std::iter;

    use ff::Field as _Field;
    use halo2curves::{bn256, CurveAffine};
    use tracing_test::traced_test;

    use crate::{
        commitment::CommitmentKey,
        plonk::{test_eval_witness::poseidon_circuit, PlonkStructure, PlonkTrace},
        polynomial::univariate::UnivariatePoly,
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

        let trace = S
            .run_sps_protocol(
                &CommitmentKey::setup(17, b""),
                &[],
                &witness,
                &mut RO::new(PoseidonSpec::new(R_F1, R_P1)),
                S.num_challenges,
            )
            .unwrap();

        (S, trace)
    }

    #[traced_test]
    #[test]
    fn zero_f() {
        let (S, trace) = poseidon_trace();
        let mut rnd = rand::thread_rng();

        let delta = Field::random(&mut rnd);
        assert!(super::compute_F(
            iter::repeat_with(|| Field::random(&mut rnd)),
            delta,
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

        let delta = Field::random(&mut rnd);
        assert_ne!(
            super::compute_F(
                iter::repeat_with(|| Field::random(&mut rnd)),
                delta,
                &S,
                &trace,
            ),
            Ok(UnivariatePoly::from_iter(
                iter::repeat(Field::ZERO).take(16)
            ))
        );
    }

    #[traced_test]
    #[test]
    fn zero_g() {
        let (S, trace) = poseidon_trace();
        let mut rnd = rand::thread_rng();

        assert!(super::compute_G(
            &S,
            iter::repeat_with(|| Field::random(&mut rnd)),
            &trace.clone(),
            &[trace],
        )
        .unwrap()
        .iter()
        .all(|f| f.is_zero().into()));
    }

    #[traced_test]
    #[test]
    fn non_zero_g() {
        let (S, mut trace) = poseidon_trace();
        let mut rnd = rand::thread_rng();
        trace
            .w
            .W
            .iter_mut()
            .for_each(|row| row.iter_mut().for_each(|el| *el = Field::random(&mut rnd)));

        assert_ne!(
            super::compute_G(
                &S,
                iter::repeat_with(|| Field::random(&mut rnd)),
                &trace.clone(),
                &[trace]
            ),
            Ok(UnivariatePoly::from_iter(
                iter::repeat(Field::ZERO).take(16)
            ))
        );
    }
}
