use std::{cell::UnsafeCell, iter};

use itertools::*;
use rayon::prelude::*;
use tracing::*;

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
#[instrument(skip_all)]
fn fold_witnesses<F: PrimeField>(
    polys_L_in_challenges: &[Box<[F]>],
    accumulator: &(impl GetWitness<F> + Sync),
    witnesses: &[impl Sync + GetWitness<F>],
) -> Vec<PlonkWitness<F>> {
    let witness_placeholder = accumulator
        .get_witness()
        .iter()
        .map(|col| vec![F::ZERO; col.len()])
        .collect();

    /// To parallelize the [`PlonkWitness`] change, we make an unsafe wrapper.
    /// It manually implements `Sync` to bypass the borrow-checker.
    ///
    /// Since we are sure that the subsequent loop only works with unique col,row pair each time
    /// and they do not overlap, we can take over this responsibility here.
    struct Wrapper<F: PrimeField> {
        data: UnsafeCell<Vec<PlonkWitness<F>>>,
    }

    impl<F: PrimeField> Wrapper<F> {
        /// Safety: this function ignores borrow-checker, you must make sure yourself that there is
        /// no data race when calling it.
        unsafe fn get<'o>(&self, cha: usize, col: usize, row: usize) -> &'o mut F {
            self.data
                .get()
                .as_mut()
                .unwrap()
                .get_unchecked_mut(cha)
                .W
                .get_unchecked_mut(col)
                .get_unchecked_mut(row)
        }
    }

    unsafe impl<F: PrimeField + Send> Sync for Wrapper<F> {}

    // TODO Make perf-allocation
    let result_matrix_by_challenge = Wrapper {
        data: UnsafeCell::new(vec![
            PlonkWitness {
                W: witness_placeholder
            };
            polys_L_in_challenges.len()
        ]),
    };

    const CHUNK_SIZE: usize = 2usize.pow(10);

    accumulator
        .get_witness()
        .par_iter()
        .enumerate()
        .flat_map(|(column, witness)| {
            rayon::iter::repeatn(column, witness.len())
                .enumerate()
                .chunks(CHUNK_SIZE)
        })
        .for_each(|chunk| {
            for (row, col) in chunk {
                for (cha_i, poly_L_i) in polys_L_in_challenges.iter().enumerate() {
                    iter::once(accumulator.get_witness())
                        .chain(witnesses.iter().map(GetWitness::get_witness))
                        .map(|w| w[col][row])
                        .zip_eq(poly_L_i)
                        .for_each(|(witness, poly_L_i_in_cha)| {
                            // Safety: each [col,row] pair is unique, so it's safe to change it directly here
                            unsafe {
                                *result_matrix_by_challenge.get(cha_i, col, row) +=
                                    *poly_L_i_in_cha * witness;
                            }
                        });
                }
            }
        });

    result_matrix_by_challenge.data.into_inner()
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
