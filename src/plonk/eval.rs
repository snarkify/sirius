use crate::polynomial::{MultiPolynomial, CHALLENGE_TYPE, POLYNOMIAL_TYPE};
use ff::PrimeField;

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("challenge index out of boundary")]
    ChallengeIndexOutOfBoundary { challenge_index: usize },
    #[error("column variable index out of boundary")]
    ColumnVariableIndexOutOfBoundary { column_index: usize },
    #[error("Invalid witness index")]
    InvalidWitnessIndex {
        num_witness: usize,
        num_advice: usize,
        num_lookup: usize,
        index: usize,
    },
    #[error("unsupported variable type")]
    UnsupportedVariableType { var_type: usize },
}

pub trait Eval<F: PrimeField> {
    type Challenges: AsRef<[F]>;
    type Selectors: AsRef<[Vec<bool>]>;
    type Fixed: AsRef<[Vec<F>]>;

    /// construct evaluation domain
    fn new() -> Self;
    fn get_challenges(&self) -> &Self::Challenges;
    fn get_selectors(&self) -> &Self::Selectors;
    fn get_fixed(&self) -> &Self::Fixed;
    /// total row size of the evaluation domain
    fn row_size(&self) -> usize {
        // at least one of them is non-empty
        if !self.get_fixed().as_ref().is_empty() {
            return self.get_fixed().as_ref()[0].len();
        } else {
            return self.get_selectors().as_ref()[0].len();
        }
    }
    fn eval_advice_var(&self, row: usize, col: usize) -> Result<F, EvalError>;
    /// evaluate a single column variable on specific row
    fn eval_column_var(&self, row: usize, index: usize) -> Result<F, EvalError> {
        let selectors = self.get_selectors();
        let fixed = self.get_fixed();
        let selector_offset = selectors.as_ref().len();
        let fixed_offset = fixed.as_ref().len() + selector_offset;
        match index {
            // selector column
            index if index < selector_offset => {
                if selectors.as_ref()[index][row] {
                    Ok(F::ONE)
                } else {
                    Ok(F::ZERO)
                }
            }
            // fixed column
            index if index < fixed_offset => Ok(fixed.as_ref()[index - selector_offset][row]),
            // advice column
            index => self.eval_advice_var(row, index - fixed_offset),
        }
    }

    fn eval_challenge(&self, index: usize) -> Result<F, EvalError> {
        if self.get_challenges().as_ref().len() <= index {
            Err(EvalError::ChallengeIndexOutOfBoundary {
                challenge_index: index,
            })
        } else {
            Ok(self.get_challenges().as_ref()[index])
        }
    }

    /// evaluate polynomial relation on specific row
    fn eval(&self, poly: &MultiPolynomial<F>, row: usize) -> Result<F, EvalError> {
        let row_size = self.row_size();
        poly.monomials
            .iter()
            .map(|mono| {
                let vars: Vec<F> = (0..mono.arity)
                    .map(|i| {
                        let (rot, col, var_type) = mono.index_to_poly[i];
                        match var_type {
                            // evaluation for challenge variable
                            CHALLENGE_TYPE => self.eval_challenge(col),
                            // evaluation for column polynomial variable
                            POLYNOMIAL_TYPE => {
                                let tmp = rot + (row as i32);
                                // TODO: double check how halo2 handle
                                // (1): row+rot < 0
                                // (2): row+rot >= row_size = 2^K
                                let row1 = if tmp < 0 {
                                    row_size as i32 + tmp
                                } else if tmp >= row_size as i32 {
                                    tmp - row_size as i32
                                } else {
                                    tmp
                                } as usize;
                                self.eval_column_var(row1, col)
                            }
                            var_type => Err(EvalError::UnsupportedVariableType { var_type }),
                        }
                    })
                    .collect::<Result<Vec<F>, EvalError>>()?;
                Ok(vars
                    .into_iter()
                    .zip(mono.exponents.iter())
                    .map(|(x, exp)| x.pow([*exp as u64, 0, 0, 0]))
                    .fold(mono.coeff, |acc, v| acc * v))
            })
            .try_fold(F::ZERO, |acc, value| match value {
                Ok(value) => Ok(acc + value),
                Err(err) => Err(err),
            })
    }
}

/// Used for evaluate compressed lookup expressions L_i(x1,...,xa) = l_i
pub struct LookupEvalDomain<'a, F: PrimeField> {
    pub(crate) challenges: Vec<F>,
    pub(crate) selectors: &'a Vec<Vec<bool>>,
    pub(crate) fixed: &'a Vec<Vec<F>>,
    pub(crate) advice: &'a Vec<Vec<F>>,
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

impl<'a, F: PrimeField> Eval<F> for LookupEvalDomain<'a, F> {
    type Challenges = Vec<F>;
    type Selectors = Vec<Vec<bool>>;
    type Fixed = Vec<Vec<F>>;
    fn new() -> Self {
        todo!()
    }

    fn get_challenges(&self) -> &Self::Challenges {
        &self.challenges
    }

    fn get_selectors(&self) -> &Self::Selectors {
        self.selectors
    }

    fn get_fixed(&self) -> &Self::Fixed {
        self.fixed
    }

    fn eval_advice_var(&self, row: usize, index: usize) -> Result<F, EvalError> {
        if index >= self.advice.len() {
            Err(EvalError::ColumnVariableIndexOutOfBoundary {
                column_index: index,
            })
        } else {
            Ok(self.advice[index][row])
        }
    }
}

impl<'a, F: PrimeField> Eval<F> for PlonkEvalDomain<'a, F> {
    type Challenges = Vec<F>;
    type Selectors = Vec<Vec<bool>>;
    type Fixed = Vec<Vec<F>>;
    fn new() -> Self {
        todo!()
    }

    fn get_challenges(&self) -> &Self::Challenges {
        &self.challenges
    }

    fn get_selectors(&self) -> &Self::Selectors {
        self.selectors
    }

    fn get_fixed(&self) -> &Self::Fixed {
        self.fixed
    }

    fn eval_advice_var(&self, row: usize, index: usize) -> Result<F, EvalError> {
        let row_size = self.row_size();
        let num_advice = self.num_advice;
        let num_lookup = self.num_lookup;
        // maximum index for one instance
        let max_width = num_advice + self.num_lookup * 4;
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

        let index_map = |index: usize| -> Result<(usize, usize), EvalError> {
            if index < self.num_advice {
                return Ok((0, index));
            }

            let lookup_index = (index - num_advice) / 4;
            let is_l_or_m = (index - num_advice) % 4 < 2;
            // 0 => l or h; 1 => m or g
            let lookup_sub_index = (index - num_advice) % 2;
            match num_witness {
                2 => {
                    if is_l_or_m {
                        Ok((0, num_advice + lookup_index * 2 + lookup_sub_index))
                    } else {
                        Ok((1, lookup_index * 2 + lookup_sub_index))
                    }
                }
                3 => {
                    if is_l_or_m {
                        Ok((1, lookup_index * 2 + lookup_sub_index))
                    } else {
                        Ok((2, lookup_index * 2 + lookup_sub_index))
                    }
                }
                num_witness => Err(EvalError::InvalidWitnessIndex {
                    num_witness,
                    num_advice,
                    num_lookup,
                    index,
                }),
            }
        };

        let (i, j) = index_map(index)?;
        if is_first_instance {
            if i >= self.W1s.len() || j >= self.W1s[i].len() {
                Err(EvalError::InvalidWitnessIndex {
                    num_witness,
                    num_advice,
                    num_lookup,
                    index,
                })
            } else {
                Ok(self.W1s[i][j * row_size + row])
            }
        } else if i >= self.W2s.len() || j >= self.W2s[i].len() {
            Err(EvalError::InvalidWitnessIndex {
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
