use std::{iter, num::NonZeroUsize};

use itertools::*;
use tracing::*;

use crate::{
    ff::PrimeField,
    fft,
    group::ff::WithSmallOrderMulGroup,
    plonk::{self, eval, GetChallenges, GetWitness, PlonkStructure},
    polynomial::{expression::QueryIndexContext, lagrange, univariate::UnivariatePoly},
    util::TryMultiProduct,
};

mod folded_witness;
pub(crate) use folded_witness::FoldedWitness;

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
    S: &PlonkStructure<F>,
    betas: impl Iterator<Item = F>,
    delta: F,
    trace: &(impl Sync + GetChallenges<F> + GetWitness<F>),
) -> Result<UnivariatePoly<F>, Error> {
    let Some(count_of_evaluation) = get_count_of_valuation(S) else {
        return Ok(UnivariatePoly::new_zeroed(0));
    };

    let leaf_count = count_of_evaluation.get().next_power_of_two().ilog2() as usize;
    let points_count = leaf_count.next_power_of_two();

    debug!(
        "count_of_evaluation: {count_of_evaluation};
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
    let betas = betas.take(leaf_count).collect::<Box<[_]>>();
    let deltas = iter::successors(Some(delta), |d| Some(d.double()))
        .take(leaf_count)
        .collect::<Box<[_]>>();

    let challenges_powers = lagrange::iter_cyclic_subgroup::<F>(points_count.ilog2())
        .map(|X| {
            betas
                .iter()
                .zip_eq(deltas.iter())
                .map(|(beta, delta)| *beta + (X * delta))
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
        .map(|result_with_evaluated_gate| {
            debug!("witness row: {:?}", result_with_evaluated_gate);
            result_with_evaluated_gate.map(Node::Leaf)
        })
        // TODO #324 Migrate to a parallel algorithm
        // TODO #324 Implement `try_tree_reduce` to stop on the first error
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
            points
                .iter()
                .zip(lagrange::iter_cyclic_subgroup::<F>(points_count.ilog2()))
                .for_each(|(res, X)| {
                    debug!("F[{X:?}] = {res:?}");
                });
            fft::ifft(&mut points);
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
    if traces.is_empty() {
        return Err(Error::EmptyTracesNotAllowed);
    }

    let Some(count_of_evaluation) = get_count_of_valuation(S) else {
        return Ok(UnivariatePoly::new_zeroed(0));
    };

    let points_count = get_points_count(S, traces.len());
    let fft_domain_size = points_count.ilog2();

    let betas_stroke = betas_stroke
        .take(count_of_evaluation.get().next_power_of_two().ilog2() as usize)
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

    let evaluated =
        FoldedWitness::new(&points_for_fft, accumulator, traces)
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
                    *left += *right * betas_stroke[l_height];
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
            fft::ifft(&mut points);
            Ok(UnivariatePoly(points))
        }
        Some(Err(err)) => Err(err.into()),
        other => unreachable!("this case must be unreachable: {other:?}"),
    }
}

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
    poly_F_in_alpha: F,
    betas_stroke: impl Iterator<Item = F>,
    accumulator: &(impl Sync + GetChallenges<F> + GetWitness<F>),
    traces: &[(impl Sync + GetChallenges<F> + GetWitness<F>)],
) -> Result<UnivariatePoly<F>, Error> {
    // is coeffs here, will transform to evals by fft later
    let poly_G = compute_G(S, betas_stroke, accumulator, traces)?;

    let points_count = poly_G.len();
    let fft_domain_size = points_count.ilog2();

    Ok(UnivariatePoly::coset_ifft(
        lagrange::iter_cyclic_subgroup::<F>(fft_domain_size)
            .map(|X| F::ZETA * X)
            .zip(poly_G.coset_fft())
            .map(|(X, poly_G_in_X)| {
                let poly_L_in_X =
                    lagrange::iter_eval_lagrange_poly_for_cyclic_group(X, fft_domain_size)
                        .next()
                        .unwrap();

                let poly_Z_in_X = lagrange::eval_vanish_polynomial(points_count, X);

                let poly_K_in_X =
                    (poly_G_in_X - (poly_F_in_alpha * poly_L_in_X)) * poly_Z_in_X.invert().unwrap();

                assert_eq!(
                    (poly_F_in_alpha * poly_L_in_X) + (poly_Z_in_X * poly_K_in_X),
                    poly_G_in_X
                );

                poly_K_in_X
            })
            .collect::<Box<[_]>>(),
    ))
}

fn get_count_of_valuation<F: PrimeField>(S: &PlonkStructure<F>) -> Option<NonZeroUsize> {
    let count_of_rows = 2usize.pow(S.k as u32);
    let count_of_gates = S.gates.len();

    NonZeroUsize::new(count_of_rows * count_of_gates)
}

fn get_points_count<F: PrimeField>(S: &PlonkStructure<F>, traces_len: usize) -> usize {
    let ctx = QueryIndexContext::from(S);
    let max_degree = S
        .gates
        .iter()
        .map(|poly| poly.degree(&ctx))
        .max()
        .unwrap_or_default();

    (traces_len * max_degree + 1).next_power_of_two()
}

#[cfg(test)]
mod test {
    use std::iter;

    use bitter::{BitReader, LittleEndianReader};
    use halo2_proofs::{
        halo2curves::ff::{PrimeField, WithSmallOrderMulGroup},
        plonk::Circuit,
    };
    use itertools::*;
    use tracing::debug;
    use tracing_test::traced_test;

    use super::{folded_witness::FoldedWitness, get_count_of_valuation, get_points_count};
    use crate::{
        commitment::CommitmentKey,
        ff::Field as _Field,
        halo2curves::{bn256, CurveAffine},
        nifs::tests::fibo_circuit_with_lookup::{get_sequence, FiboCircuitWithLookup},
        plonk::{self, test_eval_witness::poseidon_circuit, PlonkStructure, PlonkTrace},
        polynomial::{expression::QueryIndexContext, lagrange, univariate::UnivariatePoly},
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
        Spec<<Curve as CurveAffine>::Base, POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE>;

    type RO = <PoseidonRO<POSEIDON_PERMUTATION_WIDTH, POSEIDON_RATE> as random_oracle::ROPair<
        <Curve as CurveAffine>::Base,
    >>::OffCircuit;

    fn get_trace(
        k_table_size: u32,
        circuit: impl Circuit<Field>,
        instance: Vec<Field>,
    ) -> (PlonkStructure<Field>, PlonkTrace<Curve>) {
        let runner = CircuitRunner::<Field, _>::new(k_table_size, circuit, vec![]);

        let S = runner.try_collect_plonk_structure().unwrap();
        let witness = runner.try_collect_witness().unwrap();

        let PlonkTrace { u, w } = S
            .run_sps_protocol(
                &CommitmentKey::setup(17, b""),
                &instance,
                &witness,
                &mut RO::new(PoseidonSpec::new(R_F1, R_P1)),
                S.num_challenges,
            )
            .unwrap();

        (S, PlonkTrace { u, w })
    }

    fn poseidon_trace() -> (PlonkStructure<Field>, PlonkTrace<Curve>) {
        get_trace(
            13,
            poseidon_circuit::TestPoseidonCircuit::<_, 100>::default(),
            vec![Field::from(4097)],
        )
    }

    fn pow_i<'l, F: PrimeField>(
        i: usize,
        t: usize,
        challenges_powers: impl Iterator<Item = &'l F>,
    ) -> F {
        let bytes = i.to_le_bytes();
        let mut reader = LittleEndianReader::new(&bytes);

        iter::repeat_with(|| reader.read_bit().unwrap_or(false))
            .zip(challenges_powers)
            .map(|(b_j, beta_in_2j)| match b_j {
                true => *beta_in_2j,
                false => F::ONE,
            })
            .take(t)
            .reduce(|acc, coeff| acc * coeff)
            .unwrap()
    }

    #[traced_test]
    #[test]
    fn cmp_with_direct_eval_of_F() {
        let (S, mut trace) = poseidon_trace();

        let mut rnd = rand::thread_rng();
        let mut gen = iter::repeat_with(|| Field::random(&mut rnd));

        trace.w.W.iter_mut().for_each(|row| {
            row.iter_mut()
                .for_each(|v| *v = gen.by_ref().next().unwrap())
        });

        let count_of_rows = 2usize.pow(S.k as u32);
        let count_of_gates = S.gates.len();

        let count_of_evaluation = count_of_rows * count_of_gates;

        let points_count = count_of_evaluation
            .next_power_of_two()
            .ilog2()
            .next_power_of_two() as usize;

        let delta = gen.by_ref().next().unwrap();
        let betas = gen.by_ref().take(count_of_evaluation).collect::<Box<[_]>>();

        let evaluated_poly_F = super::compute_F(&S, betas.iter().copied(), delta, &trace).unwrap();

        lagrange::iter_cyclic_subgroup::<Field>(points_count.ilog2())
            .take(points_count)
            .chain(gen.take(10))
            .for_each(|X| {
                let challenge_vector = betas
                    .iter()
                    .zip(iter::successors(Some(delta), |d| Some(d.double())))
                    .take(count_of_evaluation)
                    .map(|(beta, delta)| beta + (X * delta))
                    .collect::<Box<[_]>>();

                let result_with_direct_algo = plonk::iter_evaluate_witness::<Field>(&S, &trace)
                    .enumerate()
                    .map(|(index, f_i)| {
                        pow_i(index, count_of_evaluation, challenge_vector.iter()) * f_i.unwrap()
                    })
                    .sum();

                assert_eq!(
                    evaluated_poly_F.eval(X),
                    result_with_direct_algo,
                    "not match for {X:?}"
                );
            })
    }

    #[traced_test]
    #[test]
    fn cmp_with_direct_eval_of_G() {
        let (S, trace) = poseidon_trace();
        let mut rnd = rand::thread_rng();
        let mut gen = iter::repeat_with(|| Field::random(&mut rnd));

        let count_of_rows = 2usize.pow(S.k as u32);
        let count_of_gates = S.gates.len();

        let count_of_evaluation = count_of_rows * count_of_gates;

        let beta_stroke = gen.by_ref().take(count_of_evaluation).collect::<Box<[_]>>();

        let traces = iter::repeat_with(|| {
            let mut trace = trace.clone();
            trace
                .w
                .W
                .iter_mut()
                .for_each(|row| row.iter_mut().zip(gen.by_ref()).for_each(|(v, r)| *v = r));
            trace
        })
        .take(2)
        .collect::<Box<[_]>>();

        let accumulator = trace;
        let evaluated_poly_G =
            super::compute_G(&S, beta_stroke.iter().copied(), &accumulator, &traces).unwrap();

        let max_degree = S
            .gates
            .iter()
            .map(|poly| poly.degree(&QueryIndexContext::from(&S)))
            .max()
            .unwrap_or_default();
        let points_count = (traces.len() * max_degree + 1).next_power_of_two();
        let fft_domain_size = points_count.ilog2();

        let points_for_fft = lagrange::iter_cyclic_subgroup(fft_domain_size)
            .take(points_count)
            .collect::<Box<[_]>>();

        FoldedWitness::new(&points_for_fft, &accumulator, &traces)
            .iter()
            .map(|folded_trace| plonk::iter_evaluate_witness::<Field>(&S, folded_trace))
            .zip(points_for_fft.iter().copied().chain(gen.take(10)))
            .for_each(|(folded_witness, X)| {
                let result_with_direct_algo = folded_witness
                    .enumerate()
                    .map(|(index, f_i)| {
                        pow_i(index, count_of_evaluation, beta_stroke.iter()) * f_i.unwrap()
                    })
                    .sum();

                assert_eq!(
                    evaluated_poly_G.eval(X),
                    result_with_direct_algo,
                    "for {X:?}"
                );
            });
    }

    pub fn vanish_poly<F: PrimeField>(degree: usize) -> UnivariatePoly<F> {
        let mut coeff = vec![F::ZERO; degree].into_boxed_slice();
        coeff[0] = -F::ONE;
        coeff[degree - 1] = F::ONE;
        UnivariatePoly(coeff)
    }

    #[traced_test]
    #[test]
    fn runme() {
        let (S, trace) = poseidon_trace();

        let mut rnd = rand::thread_rng();
        let mut gen = iter::repeat_with(|| Field::random(&mut rnd));

        let count_of_evaluation = get_count_of_valuation(&S).unwrap();

        let delta = gen.next().unwrap();
        let alpha = gen.next().unwrap();

        let betas = gen
            .by_ref()
            .take(count_of_evaluation.get())
            .collect::<Box<[_]>>();

        let traces = iter::repeat_with(|| {
            let mut trace = trace.clone();
            trace
                .w
                .W
                .iter_mut()
                .for_each(|row| row.iter_mut().zip(gen.by_ref()).for_each(|(v, r)| *v = r));
            trace
        })
        .take(1)
        .collect::<Box<[_]>>();
        let accumulator = traces.first().cloned().unwrap();

        let points_count = get_points_count(&S, traces.len());
        let fft_domain_size = points_count.ilog2();

        // ====== START ======
        let poly_K_rnd = UnivariatePoly::from_iter(gen.by_ref().take(points_count));

        let poly_F =
            super::compute_F::<Field>(&S, betas.iter().copied(), delta, &accumulator).unwrap();

        let poly_F_in_alpha = poly_F.eval(alpha);

        let rnd_cha_X = gen.next().unwrap();

        let poly_Z = {
            debug!("start Z");
            let poly = vanish_poly(points_count);
            assert_eq!(poly.len(), poly_K_rnd.len());

            let poly_Z_eval = |X: Field| lagrange::eval_vanish_polynomial(points_count, X);
            assert_eq!(poly.eval(rnd_cha_X), poly_Z_eval(rnd_cha_X));

            //let poly_Z_eval_dir = |X: Field| {
            //    lagrange::iter_cyclic_subgroup::<Field>(fft_domain_size)
            //        .take(points_count)
            //        .map(|a| X - a)
            //        .inspect(|c| {
            //            dbg!(c);
            //        })
            //        .fold(Field::ONE, |acc, val| acc * val)
            //};

            //assert_eq!(poly.eval(rnd_cha_X), poly_Z_eval_dir(rnd_cha_X));

            poly
        };

        let poly_L = {
            debug!("start L");
            let poly_L_eval = |X: Field| {
                lagrange::iter_eval_lagrange_poly_for_cyclic_group(X, fft_domain_size)
                    .next()
                    .unwrap()
            };
            let poly = UnivariatePoly::coset_ifft(
                lagrange::iter_cyclic_subgroup::<Field>(fft_domain_size)
                    .map(|X| X * Field::ZETA)
                    .take(points_count)
                    .map(poly_L_eval)
                    .collect(),
            );
            assert_eq!(poly.len(), poly_K_rnd.len());

            assert_eq!(poly.eval(rnd_cha_X), poly_L_eval(rnd_cha_X));

            poly
        };

        let poly_G = {
            debug!("start G");

            let poly = poly_K_rnd
                .iter()
                .zip_eq(poly_L.iter())
                .zip_eq(poly_Z.iter())
                .map(|((poly_Ki, poly_Li), poly_Zi)| {
                    (poly_F_in_alpha * poly_Li) + (poly_Zi * poly_Ki)
                })
                .collect::<UnivariatePoly<Field>>();

            lagrange::iter_cyclic_subgroup::<Field>(fft_domain_size)
                .take(points_count)
                .for_each(|cha_X| {
                    let poly_L_in_X = poly_L.eval(cha_X);
                    let poly_Z_in_X = poly_Z.eval(cha_X);
                    let poly_K_in_X = poly_K_rnd.eval(cha_X);

                    assert_eq!(
                        (poly_F_in_alpha * poly_L_in_X) + (poly_Z_in_X * poly_K_in_X),
                        poly.eval(cha_X)
                    );
                });

            poly
        };

        let poly_K = UnivariatePoly::coset_ifft(
            lagrange::iter_cyclic_subgroup::<Field>(fft_domain_size)
                .map(|X| Field::ZETA * X)
                .take(points_count)
                .map(|X| {
                    let poly_G_in_X = poly_G.eval(X);
                    let poly_L_in_X = poly_L.eval(X);
                    let poly_Z_in_X = poly_Z.eval(X);
                    let poly_K_in_X = (poly_G_in_X - (poly_F_in_alpha * poly_L_in_X))
                        * poly_Z_in_X.invert().unwrap();

                    assert_eq!(poly_K_in_X, poly_K_rnd.eval(X));

                    assert_eq!(
                        (poly_F_in_alpha * poly_L_in_X) + (poly_Z_in_X * poly_K_in_X),
                        poly_G_in_X
                    );

                    poly_K_in_X
                })
                .collect::<Box<[_]>>(),
        );

        assert_eq!(poly_K, poly_K_rnd);
    }

    #[traced_test]
    #[test]
    fn cmp_with_direct_eval_of_K() {
        let seq = get_sequence(1, 3, 2, 7);

        let (S, trace) = get_trace(
            13,
            FiboCircuitWithLookup {
                a: Field::from(seq[0]),
                b: Field::from(seq[1]),
                c: Field::from(seq[2]),
                num: 7,
            },
            vec![Field::from(4097)],
        );

        let mut rnd = rand::thread_rng();
        let mut gen = iter::repeat_with(|| Field::random(&mut rnd));

        let count_of_evaluation = get_count_of_valuation(&S).unwrap();

        let delta = gen.next().unwrap();
        let alpha = gen.next().unwrap();

        let betas = gen
            .by_ref()
            .take(count_of_evaluation.get())
            .collect::<Box<[_]>>();

        let traces = iter::repeat_with(|| {
            let mut trace = trace.clone();
            trace
                .w
                .W
                .iter_mut()
                .for_each(|row| row.iter_mut().zip(gen.by_ref()).for_each(|(v, r)| *v = r));
            trace
        })
        .take(5)
        .collect::<Box<[_]>>();

        let accumulator = traces.first().cloned().unwrap();

        let betas_stroke = super::PolyChallenges {
            betas: betas.clone(),
            delta,
            alpha,
        }
        .iter_beta_stroke()
        .collect::<Box<[_]>>();

        let poly_F =
            super::compute_F::<Field>(&S, betas.iter().copied(), delta, &accumulator).unwrap();

        let poly_G =
            super::compute_G(&S, betas_stroke.iter().copied(), &accumulator, &traces).unwrap();

        let poly_K = super::compute_K::<Field>(
            &S,
            poly_F.eval(alpha),
            betas_stroke.iter().copied(),
            &accumulator,
            &traces,
        )
        .unwrap();

        let points_count = get_points_count(&S, traces.len());
        let fft_domain_size = points_count.ilog2();

        let poly_F_in_alpha = poly_F.eval(alpha);
        let poly_L_eval = |X: Field| {
            lagrange::iter_eval_lagrange_poly_for_cyclic_group(X, fft_domain_size)
                .next()
                .unwrap()
        };

        let poly_Z_eval = |X: Field| lagrange::eval_vanish_polynomial(points_count, X);

        lagrange::iter_cyclic_subgroup::<Field>(fft_domain_size)
            .map(|pt| Field::ZETA * pt)
            .take(points_count)
            .chain(
                gen.take(10)
                    .inspect(|X| debug!("start with random X: {X:?}")),
            )
            .for_each(|cha_X| {
                let poly_G_in_X = poly_G.eval(cha_X);
                let poly_K_in_X = poly_K.eval(cha_X);
                let poly_L_in_X = poly_L_eval(cha_X);
                let poly_Z_in_X = poly_Z_eval(cha_X);

                let poly_G_in_X_calculated =
                    (poly_F_in_alpha * poly_L_in_X) + (poly_Z_in_X * poly_K_in_X);

                // G(X) = F(alpha) * L(X) + Z(X) * K(X)
                assert_eq!(poly_G_in_X_calculated, poly_G_in_X, "for {cha_X:?}");
            });
    }

    #[traced_test]
    #[test]
    fn zero_f() {
        let (S, trace) = poseidon_trace();
        let mut rnd = rand::thread_rng();

        let delta = Field::random(&mut rnd);
        assert!(super::compute_F(
            &S,
            iter::repeat_with(move || Field::random(&mut rnd)),
            delta,
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
                &S,
                iter::repeat_with(|| Field::random(&mut rnd)),
                delta,
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
