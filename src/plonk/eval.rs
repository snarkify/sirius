use crate::plonk::RelaxedPlonkWitness;
use crate::polynomial::{MultiPolynomial, CHALLENGE_TYPE, POLYNOMIAL_TYPE};
use ff::PrimeField;

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("challenge index out of boundary")]
    ChallengeIndexOutOfBoundary { challenge_index: usize },
    #[error("column variable index out of boundary")]
    ColumnVariableIndexOutOfBoundary { column_index: usize },
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
        self.get_fixed().as_ref().len()
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
            index => self.eval_advice_var(row, index - fixed_offset), // index if index < max_offset => Ok(self.table.advice_columns[index - fixed_offset][row]),
        }
    }

    fn eval_challenge(&self, index: usize) -> Result<F, EvalError> {
        if self.get_challenges().as_ref().len() >= index {
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
                            POLYNOMIAL_TYPE => {
                                // evaluation for column polynomial variable
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

/// Used for evaluate plonk custom gates
pub struct PlonkEvalDomain<'a, F: PrimeField> {
    pub(crate) challenges: Vec<F>,
    pub(crate) selectors: &'a Vec<Vec<bool>>,
    pub(crate) fixed: &'a Vec<Vec<F>>,
    pub(crate) W: &'a RelaxedPlonkWitness<F>,
}

/// Used for evaluate cross terms T[i]
pub struct CrossTermEvalDomain<'a, F: PrimeField> {
    // concatenation of challenges from two RelaxedPlonkInstance
    pub(crate) challenges: Vec<F>,
    pub(crate) selectors: &'a Vec<Vec<bool>>,
    pub(crate) fixed: &'a Vec<Vec<F>>,
    pub(crate) W1: &'a RelaxedPlonkWitness<F>,
    pub(crate) W2: &'a RelaxedPlonkWitness<F>,
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
        todo!()
    }
}

impl<'a, F: PrimeField> Eval<F> for CrossTermEvalDomain<'a, F> {
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
        todo!()
    }
}
