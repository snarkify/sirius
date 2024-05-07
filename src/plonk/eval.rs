use crate::polynomial::ColumnIndex;
use ff::PrimeField;

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    #[error("challenge index out of boundary: {challenge_index}")]
    ChallengeIndexOutOfBoundary {
        challenge_index: usize,
        challeges_len: usize,
    },
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
        let challenges = self.get_challenges().as_ref();
        challenges
            .get(index)
            .copied()
            .ok_or(Error::ChallengeIndexOutOfBoundary {
                challenge_index: index,
                challeges_len: challenges.len(),
            })
    }
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
