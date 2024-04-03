use crate::polynomial::{
    graph_evaluator::GraphEvaluator, grouped_poly::GroupedPoly, ColumnIndex, Expression,
    MultiPolynomial,
};
use ff::PrimeField;
use rayon::prelude::*;
use std::collections::HashMap;

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    #[error("challenge index out of boundary: {challenge_index}")]
    ChallengeIndexOutOfBoundary { challenge_index: usize },
    #[error("column variable index out of boundary: {column_index}")]
    ColumnVariableIndexOutOfBoundary { column_index: usize },
    #[error("column variable row index out of boundary: {row_index}")]
    RowIndexOutOfBoundary { row_index: usize },
    #[error("InvalidExpression")]
    InvalidExpression,
    #[error("Invalid witness index. num_witness: {num_witness}, num_advice: {num_advice}, num_lookup: {num_lookup}, index: {index}")]
    InvalidWitnessIndex {
        num_witness: usize,
        num_advice: usize,
        num_lookup: usize,
        index: usize,
    },
    #[error("unsupported variable type: {var_type:?}")]
    UnsupportedVariableType { var_type: ColumnIndex },
}

/// Provides a contract for retrieving evaluation data necessary for evaluating of poly
///
/// Implementors of this trait are responsible for providing access to various
/// kinds of data: challenges, selectors, fixed columns, etc.
pub trait GetDataForEval<F: PrimeField> {
    fn get_challenges(&self) -> &impl AsRef<[F]>;
    fn get_selectors(&self) -> &impl AsRef<[Vec<bool>]>;
    fn get_fixed(&self) -> &impl AsRef<[Vec<F>]>;

    fn num_lookup(&self) -> usize;
    fn num_selectors(&self) -> usize {
        self.get_selectors().as_ref().len()
    }
    fn num_fixed(&self) -> usize {
        self.get_fixed().as_ref().len()
    }

    fn eval_advice_var(&self, row_index: usize, colulm_index: usize) -> Result<F, Error>;

    /// Total row size of the evaluation domain
    fn row_size(&self) -> usize {
        self.get_fixed()
            .as_ref()
            .first()
            .map(Vec::len)
            .or_else(|| self.get_selectors().as_ref().first().map(Vec::len))
            .expect("Fixed & Selectors can't be empty in one time")
    }

    /// evaluate a single column variable on specific row
    fn eval_column_var(&self, row: usize, index: usize) -> Result<F, Error> {
        let selectors = self.get_selectors().as_ref();
        let fixed = self.get_fixed().as_ref();

        selectors
            .get(index)
            .map(|selector| if selector[row] { F::ONE } else { F::ZERO })
            .or_else(|| fixed.get(index - selectors.len()).map(|fixed| fixed[row]))
            .map_or_else(
                || self.eval_advice_var(row, index - selectors.len() - fixed.len()),
                Ok,
            )
    }

    fn eval_challenge(&self, index: usize) -> Result<F, Error> {
        self.get_challenges().as_ref().get(index).copied().ok_or(
            Error::ChallengeIndexOutOfBoundary {
                challenge_index: index,
            },
        )
    }
}

/// The `Eval` trait is used to evaluate multi-variable polynomials in a Evaluation Domain defined
/// over a prime field `F`
///
/// This trait encapsulates the necessary functionality to evaluate polynomials
///
/// # Generic Parameters
///
/// * `F`: The prime field over which the evaluations are carried out.
/// * `POLY`: The type of polynomial or expression to be evaluated.
///
pub trait Eval<F: PrimeField, POLY>: GetDataForEval<F> {
    /// General method allowing to perform calculations of input polynomial type on the basis of
    /// data requested in `GetEvalData`. Depending on its representation the implementation may
    /// differ
    fn eval(&self, poly: &POLY, row_index: usize) -> Result<F, Error>;
}

impl<F: PrimeField, E: GetDataForEval<F>> Eval<F, MultiPolynomial<F>> for E {
    /// Evaluate virtual multi-polynomial (i.e. custom gates, cross-term expressions etc) on
    /// specific row to evaluate each monomial term of the form
    /// ```math
    /// $c*x1[row]^{k1}*x2[row]^{k2}*\cdots$
    /// ```
    /// we first lookup the value of `$x[row]$` from the Evaluation domain, then calculate the
    /// value of monomial. to speedup, we will save the x and `x^k` in a HashMap
    fn eval(&self, poly: &MultiPolynomial<F>, row_index: usize) -> Result<F, Error> {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        struct Index<'l> {
            column_index: &'l ColumnIndex,
            exp: &'l usize,
        }
        let mut evals = HashMap::<Index<'_>, _>::with_capacity(poly.degree() * poly.arity());

        let row_size = self.row_size() as i32;
        poly.monomials
            .iter()
            .map(|mono| {
                mono.index_to_poly
                    .iter()
                    .take(mono.arity)
                    .zip(mono.exponents.iter())
                    .map(|(column_index, exp)| {
                        if *exp == 0 {
                            return Ok(F::ONE);
                        }
                        if let Some(vn) = evals.get(&Index { column_index, exp }) {
                            Ok(*vn)
                        } else if let Some(v1) = evals.get(&Index {
                            column_index,
                            exp: &1,
                        }) {
                            let vn = v1.pow([*exp as u64, 0, 0, 0]);
                            evals.insert(Index { column_index, exp }, vn);
                            Ok(vn)
                        } else {
                            let v1 = match column_index {
                                // evaluation for challenge variable
                                ColumnIndex::Challenge { column_index } => {
                                    self.eval_challenge(*column_index)
                                }
                                // evaluation for column polynomial variable
                                ColumnIndex::Polynominal {
                                    rotation,
                                    column_index,
                                } => {
                                    let rotation_plus_row = rotation + (row_index as i32);
                                    // TODO: double check how halo2 handle
                                    // (1): row+rot < 0
                                    // (2): row+rot >= row_size = 2^K
                                    let row = if rotation_plus_row < 0 {
                                        rotation_plus_row + row_size
                                    } else if rotation_plus_row >= row_size {
                                        rotation_plus_row - row_size
                                    } else {
                                        rotation_plus_row
                                    };
                                    self.eval_column_var(row as usize, *column_index)
                                }
                            }?;

                            evals
                                .entry(Index {
                                    column_index,
                                    exp: &1,
                                })
                                .or_insert_with(|| v1.pow([1, 0, 0, 0]));

                            Ok(*evals
                                .entry(Index { column_index, exp })
                                .or_insert_with(|| v1.pow([*exp as u64, 0, 0, 0])))
                        }
                    })
                    .try_fold(
                        mono.coeff,
                        |acc, result_with_var| Ok(acc * result_with_var?),
                    )
            })
            .try_fold(F::ZERO, |acc, value| Ok(acc + value?))
    }
}

impl<F: PrimeField, E: GetDataForEval<F>> Eval<F, Expression<F>> for E {
    fn eval(&self, expr: &Expression<F>, row_index: usize) -> Result<F, Error> {
        GraphEvaluator::new(expr).evaluate(self, row_index)
    }
}

pub fn eval_grouped<F: PrimeField>(
    data: &(impl GetDataForEval<F> + Sync),
    poly: &GroupedPoly<F>,
) -> Result<Vec<Box<[F]>>, Error> {
    let row_size = data.row_size();
    poly.iter()
        .map(|expr| match expr {
            Some(expr) => {
                let evaluator = GraphEvaluator::new(expr);

                (0..row_size)
                    .into_par_iter()
                    .map(|row_index| evaluator.evaluate(data, row_index))
                    .collect::<Result<Box<[_]>, _>>()
            }
            None => Ok(vec![F::ZERO; row_size].into_boxed_slice()),
        })
        .collect::<Result<Vec<Box<[F]>>, Error>>()
}

/// Used for evaluate compressed lookup expressions L_i(x1,...,xa) = l_i
pub struct LookupEvalDomain<'a, F: PrimeField> {
    pub(crate) num_lookup: usize,
    pub(crate) challenges: Vec<F>,
    pub(crate) selectors: &'a Vec<Vec<bool>>,
    pub(crate) fixed: &'a Vec<Vec<F>>,
    pub(crate) advice: &'a [Vec<F>],
}

/// Used for evaluate cross terms T[i]
pub struct PlonkEvalDomain<'a, F: PrimeField> {
    pub(crate) num_advice: usize,
    pub(crate) num_lookup: usize,
    // concatenation of challenges from two RelaxedPlonkInstance
    pub(crate) challenges: Vec<F>,
    pub(crate) selectors: &'a Vec<Vec<bool>>,
    pub(crate) fixed: &'a Vec<Vec<F>>,
    // [`RelaxedPlonkWitness::W`] for first instance
    pub(crate) W1s: &'a Vec<Vec<F>>,
    // [`RelaxedPlonkWitness::W`] for second instance
    pub(crate) W2s: &'a Vec<Vec<F>>,
}

impl<'a, F: PrimeField> GetDataForEval<F> for LookupEvalDomain<'a, F> {
    fn num_lookup(&self) -> usize {
        self.num_lookup
    }

    fn get_challenges(&self) -> &impl AsRef<[F]> {
        &self.challenges
    }

    fn get_selectors(&self) -> &impl AsRef<[Vec<bool>]> {
        self.selectors
    }

    fn get_fixed(&self) -> &impl AsRef<[Vec<F>]> {
        self.fixed
    }

    fn eval_advice_var(&self, row: usize, index: usize) -> Result<F, Error> {
        if index >= self.advice.len() {
            Err(Error::ColumnVariableIndexOutOfBoundary {
                column_index: index,
            })
        } else if row >= self.advice[index].len() {
            Err(Error::RowIndexOutOfBoundary { row_index: row })
        } else {
            Ok(self.advice[index][row])
        }
    }
}

impl<'a, F: PrimeField> GetDataForEval<F> for PlonkEvalDomain<'a, F> {
    fn num_lookup(&self) -> usize {
        self.num_lookup
    }

    fn get_challenges(&self) -> &impl AsRef<[F]> {
        &self.challenges
    }

    fn get_selectors(&self) -> &impl AsRef<[Vec<bool>]> {
        self.selectors
    }

    fn get_fixed(&self) -> &impl AsRef<[Vec<F>]> {
        self.fixed
    }

    fn eval_advice_var(&self, row: usize, index: usize) -> Result<F, Error> {
        let row_size = self.row_size();
        let num_advice = self.num_advice;
        let num_lookup = self.num_lookup();
        // maximum index for one instance
        let max_width = num_advice + num_lookup * 5;
        let (is_first_instance, index) = if index < max_width {
            (true, index)
        } else {
            (false, index - max_width)
        };
        let num_witness = if is_first_instance {
            self.W1s.len()
        } else {
            self.W2s.len()
        };

        let index_map = |index: usize| -> Result<(usize, usize), Error> {
            if index < num_advice {
                return Ok((0, index));
            }

            let lookup_index = (index - num_advice) / 5;
            let lookup_sub_index = (index - num_advice) % 5;
            let (is_first_round, lookup_sub_index) = if lookup_sub_index < 3 {
                (true, lookup_sub_index)
            } else {
                (false, lookup_sub_index - 3)
            };
            match num_witness {
                2 => {
                    if is_first_round {
                        Ok((0, num_advice + lookup_index * 3 + lookup_sub_index))
                    } else {
                        Ok((1, lookup_index * 2 + lookup_sub_index))
                    }
                }
                3 => {
                    if is_first_round {
                        Ok((1, lookup_index * 3 + lookup_sub_index))
                    } else {
                        Ok((2, lookup_index * 2 + lookup_sub_index))
                    }
                }
                num_witness => Err(Error::InvalidWitnessIndex {
                    num_witness,
                    num_advice,
                    num_lookup,
                    index,
                }),
            }
        };

        let (i, j) = index_map(index)?;
        if is_first_instance {
            if self.W1s.len() <= i || self.W1s[i].len() <= j * row_size + row {
                Err(Error::InvalidWitnessIndex {
                    num_witness,
                    num_advice,
                    num_lookup,
                    index,
                })
            } else {
                Ok(self.W1s[i][j * row_size + row])
            }
        } else if self.W2s.len() <= i || self.W2s[i].len() <= j * row_size + row {
            Err(Error::InvalidWitnessIndex {
                num_witness,
                num_advice,
                num_lookup,
                index,
            })
        } else {
            Ok(self.W2s[i][j * row_size + row])
        }
    }
}
