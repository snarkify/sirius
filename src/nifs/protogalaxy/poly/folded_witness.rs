use std::iter;

use itertools::*;
use rayon::prelude::*;

use crate::{
    ff::PrimeField,
    plonk::{GetChallenges, GetWitness, PlonkWitness},
    polynomial::lagrange,
    util::MultiCartesianProduct,
};

pub(crate) struct FoldedWitness<F: PrimeField> {
    witness: PlonkWitness<F>,
    challenges: Vec<F>,
}

impl<F: PrimeField> FoldedWitness<F> {
    pub(crate) fn new(
        points_for_fft: &[F],
        lagrange_domain: u32,
        accumulator: &(impl Sync + GetChallenges<F> + GetWitness<F>),
        traces: &[(impl Sync + GetChallenges<F> + GetWitness<F>)],
    ) -> Box<[Self]> {
        let polys_L_in_challenges = points_for_fft
            .iter()
            .map(|X| {
                lagrange::iter_eval_lagrange_poly_for_cyclic_group(*X, lagrange_domain)
                    .collect::<Box<[_]>>()
            })
            .collect::<Box<[_]>>();

        let folded_witnesses_collection =
            fold_witnesses(&polys_L_in_challenges, accumulator, traces);
        let folded_challenges_collection =
            fold_plonk_challenges(&polys_L_in_challenges, accumulator, traces);

        folded_witnesses_collection
            .into_iter()
            .zip_eq(folded_challenges_collection)
            .map(|(witness, challenges)| Self {
                witness,
                challenges,
            })
            .collect()
    }
}
impl<F: PrimeField> GetChallenges<F> for FoldedWitness<F> {
    fn get_challenges(&self) -> &[F] {
        &self.challenges
    }
}
impl<F: PrimeField> GetWitness<F> for FoldedWitness<F> {
    fn get_witness(&self) -> &[Vec<F>] {
        &self.witness.W
    }
}

/// For each `X` we must perform the operation of sum all all matrices [`PlonkWitness`] with
/// coefficients taken from [`lagrange::iter_eval_lagrange_polynomials_for_cyclic_group`]
///
/// Since the number of rows is large, we do this in one pass, counting the points for each
/// challenge at each iteration, and laying them out in separate [`PlonkWitness`] at the end.
fn fold_witnesses<F: PrimeField>(
    polys_L_in_challenges: &[Box<[F]>],
    accumulator: &(impl GetWitness<F> + Sync),
    witnesses: &[impl Sync + GetWitness<F>],
) -> Vec<PlonkWitness<F>> {
    let witness_placeholder = accumulator.get_witness().to_vec();

    // TODO Create on the fly to avoid multiple rows iterations
    let mut result_matrix_by_challenge = vec![
        PlonkWitness {
            W: witness_placeholder
        };
        polys_L_in_challenges.len()
    ];

    accumulator
        .get_witness()
        .iter()
        .enumerate()
        .flat_map(|(column, witness)| {
            let rows_count = witness.len();
            iter::repeat(column).zip(0..rows_count)
        })
        .map(|(col, row)| {
            iter::once(accumulator.get_witness())
                .chain(witnesses.iter().map(GetWitness::get_witness))
                .map(|witness| witness[col][row])
                .zip(
                    polys_L_in_challenges
                        .iter()
                        .map(|m| m.iter().copied())
                        .multi_product(),
                )
                // Element of iterator:
                // ```
                // (w0_00, [L0(X0),  L0(X1), ...])
                // (w0_01, [L0(X0),  L0(X1), ...])
                // ...
                // (w1_00, [L1(X0),  L1(X1), ...])
                // (w1_01, [L1(X0),  L1(X1), ...])
                // ...
                // ```
                //
                // The next `fold` call doing next action:
                // (w0_ij, [L0(X0),  L0(X1), ...]) + (w1_ij, [L1(X0),  L1(X1), ...])
                .fold(
                    vec![F::ZERO; polys_L_in_challenges.len()].into_boxed_slice(),
                    // every element of this collection - one cell for each `X_challenge`
                    |mut cells_by_challenge, (witness, lagrange_by_challenge)| {
                        cells_by_challenge
                            .iter_mut()
                            .zip(lagrange_by_challenge.iter())
                            .for_each(|(res, poly_L_i_in_X)| {
                                *res += *poly_L_i_in_X * witness;
                            });

                        cells_by_challenge
                    },
                )
        })
        .zip(
            // Here we take an iterator that on each iteration returns [column][row] elements for
            // each witness for its challenge
            //
            // next -> [
            //     result[0][col][row],
            //     result[1][col][row],
            //     ...,
            //     result[challenges_len][col][row]
            // ]
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
    polys_L_in_challenges: &[Box<[F]>],
    accumulator: &(impl GetChallenges<F> + Sync),
    plonk_challenges: &[impl Sync + GetChallenges<F>],
) -> Vec<Vec<F>> {
    let plonk_challenges_len = accumulator.get_challenges().len();

    iter::once(accumulator.get_challenges())
        .chain(plonk_challenges.iter().map(GetChallenges::get_challenges))
        .zip(
            polys_L_in_challenges
                .iter()
                .map(|m| m.iter().copied())
                .multi_product(),
        )
        .fold(
            vec![vec![F::ZERO; plonk_challenges_len]; polys_L_in_challenges.len()],
            |mut folded, (plonk_challenge, lagrange_by_X_challenges)| {
                folded
                    .iter_mut()
                    .zip(lagrange_by_X_challenges.iter())
                    .for_each(
                        |(folded_plonk_challenge, lagrange_multiplier_by_plonk_challenge)| {
                            folded_plonk_challenge
                                .iter_mut()
                                .zip(plonk_challenge)
                                .for_each(|(folded, element)| {
                                    *folded += *element * lagrange_multiplier_by_plonk_challenge;
                                });
                        },
                    );

                folded
            },
        )
}
