use ff::{Field, PrimeField};
use halo2_proofs::poly::Rotation;
use halo2curves::CurveAffine;
use tracing::*;

use crate::plonk::eval::Eval;

use super::Expression;

/// Return the index in the polynomial of size `isize` after rotation `rot`.
fn get_rotation_idx(idx: usize, rot: i32, num_row: usize) -> usize {
    (((idx as i32) + rot).rem_euclid(num_row as i32)) as usize
}

/// Value used in a calculation
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd)]
pub enum ValueSource {
    /// This is a constant value
    Constant(usize),
    /// This is an intermediate value
    Intermediate(usize),
    /// This is a fixed column
    Fixed { index: usize, rotation: usize },
    /// This is an advice (witness) column
    Poly { index: usize, rotation: usize },
    /// This is a challenge
    Challenge { index: usize },
}

/// Calculation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Calculation {
    /// This is an addition
    Add(ValueSource, ValueSource),
    /// This is a subtraction
    Sub(ValueSource, ValueSource),
    /// This is a product
    Mul(ValueSource, ValueSource),
    /// This is a square
    Square(ValueSource),
    /// This is a double
    Double(ValueSource),
    /// This is a negation
    Negate(ValueSource),
    /// This is Horner's rule: `val = a; val = val * c + b[]`
    Horner(ValueSource, Vec<ValueSource>, ValueSource),
    /// This is a simple assignment
    Store(ValueSource),
}

impl Calculation {
    /// Get the resulting value of this calculation
    pub fn evaluate<F: PrimeField>(
        &self,
        rotations: &[usize],
        constants: &[F],
        intermediates: &[F],
        eval_getter: &impl Eval<F>,
    ) -> F {
        let get_value = |value: &ValueSource| -> F {
            match value {
                ValueSource::Constant(id) => constants[*id],
                ValueSource::Intermediate(id) => intermediates[*id],
                ValueSource::Fixed { index, rotation } => {
                    eval_getter.get_fixed().as_ref()[*index][rotations[*rotation]]
                }
                ValueSource::Poly { index, rotation } => eval_getter
                    .eval_column_var(rotations[*rotation], *index)
                    .expect("TODO"),
                ValueSource::Challenge { index } => *eval_getter
                    .get_challenges()
                    .as_ref()
                    .get(*index)
                    .expect("TODO"),
            }
        };

        match self {
            Calculation::Add(a, b) => get_value(a) + get_value(b),
            Calculation::Sub(a, b) => get_value(a) - get_value(b),
            Calculation::Mul(a, b) => get_value(a) * get_value(b),
            Calculation::Square(v) => get_value(v).square(),
            Calculation::Double(v) => get_value(v).double(),
            Calculation::Negate(v) => -get_value(v),
            Calculation::Horner(start_value, parts, factor) => {
                let factor = get_value(factor);
                let mut value = get_value(start_value);
                for part in parts.iter() {
                    value = value * factor + get_value(part);
                }
                value
            }
            Calculation::Store(v) => get_value(v),
        }
    }
}

/// CaluclationInfo
#[derive(Clone, Debug)]
pub struct CalculationInfo {
    /// Calculation
    pub calculation: Calculation,
    /// Target
    pub target: usize,
}

/// EvaluationData
#[derive(Default, Debug)]
pub struct EvaluationData<C: CurveAffine> {
    /// Intermediates
    pub intermediates: Vec<C::ScalarExt>,
    /// Rotations
    pub rotations: Vec<usize>,
}

/// GraphEvaluator
#[derive(Clone, Debug)]
pub struct GraphEvaluator<C: CurveAffine> {
    /// Constants
    /// TODO #159 Consider better ways of storage (sorted for example)
    pub constants: Vec<C::ScalarExt>,
    /// Rotations
    pub rotations: Vec<i32>,
    /// Calculations
    pub calculations: Vec<CalculationInfo>,
    /// Number of intermediates
    pub num_intermediates: usize,
}

impl<C: CurveAffine + Default> Default for GraphEvaluator<C> {
    fn default() -> Self {
        Self {
            // The most used constants are added here, for simplicity's sake
            constants: vec![
                C::ScalarExt::ZERO,
                C::ScalarExt::ONE,
                C::ScalarExt::from(2u64),
            ],
            rotations: Default::default(),
            calculations: Default::default(),
            num_intermediates: Default::default(),
        }
    }
}

impl<C: CurveAffine> GraphEvaluator<C> {
    #[instrument(name = "GraphEvaluator::new", skip_all)]
    pub fn new(expr: &Expression<C::ScalarExt>) -> Self {
        let mut self_ = GraphEvaluator::default();

        debug!("from {expr:?}"); // TODO Remove, too big log line
        let value_source = self_.add_expression(expr);
        self_.add_calculation(Calculation::Store(value_source));

        self_
    }

    /// Adds a rotation
    fn add_rotation(&mut self, rotation: &Rotation) -> usize {
        match self.rotations.iter().position(|&c| c == rotation.0) {
            Some(index) => {
                debug!("rotation {rotation:?} already have index: {index}, will use it");
                index
            }
            None => {
                self.rotations.push(rotation.0);
                let index = self.rotations.len() - 1;
                debug!("rotation {rotation:?} have't index, add it with index: {index}");
                index
            }
        }
    }

    /// Adds a constant
    fn add_constant(&mut self, constant: &C::ScalarExt) -> ValueSource {
        ValueSource::Constant(match self.constants.iter().position(|&c| c == *constant) {
            Some(index) => {
                debug!("constant {constant:?} already have index: {index}, will use it");
                index
            }
            None => {
                self.constants.push(*constant);
                let index = self.constants.len() - 1;
                debug!("constant {constant:?} have't index, add it with index: {index}");
                index
            }
        })
    }

    /// Adds a calculation.
    /// Currently does the simplest thing possible: just stores the
    /// resulting value so the result can be reused  when that calculation
    /// is done multiple times.
    fn add_calculation(&mut self, calculation: Calculation) -> ValueSource {
        let existing_calculation = self
            .calculations
            .iter()
            .find(|c| c.calculation == calculation);
        match existing_calculation {
            Some(existing_calculation) => ValueSource::Intermediate(existing_calculation.target),
            None => {
                let target = self.num_intermediates;
                self.calculations.push(CalculationInfo {
                    calculation,
                    target,
                });
                self.num_intermediates += 1;
                ValueSource::Intermediate(target)
            }
        }
    }

    /// Generates an optimized evaluation for the expression
    fn add_expression(&mut self, expr: &Expression<C::ScalarExt>) -> ValueSource {
        match expr {
            Expression::Constant(scalar) => self.add_constant(scalar),
            Expression::Polynomial(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Poly {
                    index: query.index,
                    rotation: rot_idx,
                }))
            }
            Expression::Challenge(challenge_index) => {
                self.add_calculation(Calculation::Store(ValueSource::Challenge {
                    index: *challenge_index,
                }))
            }
            Expression::Negated(a) => match **a {
                Expression::Constant(scalar) => self.add_constant(&-scalar),
                _ => {
                    let result_a = self.add_expression(a);
                    match result_a {
                        ValueSource::Constant(0) => result_a,
                        _ => self.add_calculation(Calculation::Negate(result_a)),
                    }
                }
            },
            Expression::Sum(a, b) => {
                // Undo subtraction stored as a + (-b) in expressions
                match &**b {
                    Expression::Negated(b_int) => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b_int);
                        if result_a == ValueSource::Constant(0) {
                            self.add_calculation(Calculation::Negate(result_b))
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else {
                            self.add_calculation(Calculation::Sub(result_a, result_b))
                        }
                    }
                    _ => {
                        let expr_a_value_source = self.add_expression(a);
                        let expr_b_value_source = self.add_expression(b);

                        if expr_a_value_source <= expr_b_value_source {
                            self.add_calculation(Calculation::Add(
                                expr_a_value_source,
                                expr_b_value_source,
                            ))
                        } else {
                            self.add_calculation(Calculation::Add(
                                expr_b_value_source,
                                expr_a_value_source,
                            ))
                        }
                    }
                }
            }
            Expression::Product(a, b) => {
                let result_a = self.add_expression(a);
                let result_b = self.add_expression(b);
                if result_a == ValueSource::Constant(0) || result_b == ValueSource::Constant(0) {
                    ValueSource::Constant(0)
                } else if result_a == ValueSource::Constant(1) {
                    result_b
                } else if result_b == ValueSource::Constant(1) {
                    result_a
                } else if result_a == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_b))
                } else if result_b == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_a))
                } else if result_a == result_b {
                    self.add_calculation(Calculation::Square(result_a))
                } else if result_a <= result_b {
                    self.add_calculation(Calculation::Mul(result_a, result_b))
                } else {
                    self.add_calculation(Calculation::Mul(result_b, result_a))
                }
            }
            Expression::Scaled(a, f) => {
                if *f == C::ScalarExt::ZERO {
                    ValueSource::Constant(0)
                } else if *f == C::ScalarExt::ONE {
                    self.add_expression(a)
                } else {
                    let cst = self.add_constant(f);
                    let result_a = self.add_expression(a);
                    self.add_calculation(Calculation::Mul(result_a, cst))
                }
            }
        }
    }

    /// Creates a new evaluation structure
    pub fn instance(&self) -> EvaluationData<C> {
        EvaluationData {
            intermediates: vec![C::ScalarExt::ZERO; self.num_intermediates],
            rotations: vec![0usize; self.rotations.len()],
        }
    }

    #[instrument(name = "GraphEvaluator::evaluate", skip_all)]
    pub fn evaluate(&self, getter: &impl Eval<C::ScalarExt>, idx: usize) -> C::ScalarExt {
        let mut data = self.instance();
        // All rotation index values
        for (rot_idx, rot) in self.rotations.iter().enumerate() {
            data.rotations[rot_idx] = get_rotation_idx(idx, *rot, getter.num_row());
        }

        // All calculations, with cached intermediate results
        for calc in self.calculations.iter() {
            debug!("start calc: {calc:?}");
            data.intermediates[calc.target] = calc.calculation.evaluate(
                &data.rotations,
                &self.constants,
                &data.intermediates,
                getter,
            );
        }

        // Return the result of the last calculation (if any)
        if let Some(calc) = self.calculations.last() {
            data.intermediates[calc.target]
        } else {
            C::ScalarExt::ZERO
        }
    }
}

#[cfg(test)]
mod tests {
    use std::array;

    use halo2curves::bn256;
    use tracing_test::traced_test;

    use crate::{
        plonk::eval::{Error as EvalError, GetEvaluateData},
        polynomial::Query,
    };

    use super::*;

    #[derive(Default)]
    struct Mock<F: PrimeField> {
        challenges: Vec<F>,
        selectors: Vec<Vec<bool>>,
        fixed: Vec<Vec<F>>,
        advice: Vec<Vec<F>>,
        num_lookup: usize,
    }

    impl<F: PrimeField> GetEvaluateData<F> for Mock<F> {
        fn get_challenges(&self) -> &impl AsRef<[F]> {
            &self.challenges
        }

        fn get_selectors(&self) -> &impl AsRef<[Vec<bool>]> {
            &self.selectors
        }

        fn get_fixed(&self) -> &impl AsRef<[Vec<F>]> {
            &self.fixed
        }

        fn eval_advice_var(&self, row_index: usize, column_index: usize) -> Result<F, EvalError> {
            self.advice
                .get(column_index)
                .ok_or(EvalError::ColumnVariableIndexOutOfBoundary { column_index })
                .and_then(|column| {
                    column
                        .get(row_index)
                        .ok_or(EvalError::RowIndexOutOfBoundary { row_index })
                })
                .cloned()
        }

        fn num_lookup(&self) -> usize {
            self.num_lookup
        }
    }

    type C1 = bn256::G1Affine;
    type Scalar = <C1 as CurveAffine>::ScalarExt;

    #[traced_test]
    #[test]
    fn constant() {
        let val = Scalar::random(&mut rand::thread_rng());

        assert_eq!(
            GraphEvaluator::<C1>::new(&Expression::Constant(val)).evaluate(&Mock::default(), 0),
            val
        );
    }

    #[traced_test]
    #[test]
    fn sum_const() {
        let mut rnd = rand::thread_rng();
        let lhs = Scalar::random(&mut rnd);
        let rhs = Scalar::random(&mut rnd);

        let res = GraphEvaluator::<C1>::new(&Expression::Sum(
            Box::new(Expression::Constant(lhs)),
            Box::new(Expression::Constant(rhs)),
        ))
        .evaluate(&Mock::default(), 0);

        assert_eq!(res, lhs + rhs);
    }

    #[traced_test]
    #[test]
    fn product_const() {
        let mut rnd = rand::thread_rng();
        let lhs = Scalar::random(&mut rnd);
        let rhs = Scalar::random(&mut rnd);

        let res = GraphEvaluator::<C1>::new(&Expression::Product(
            Box::new(Expression::Constant(lhs)),
            Box::new(Expression::Constant(rhs)),
        ))
        .evaluate(&Mock::default(), 0);

        assert_eq!(res, lhs * rhs);
    }

    #[traced_test]
    #[test]
    fn neg_const() {
        let value = Scalar::random(&mut rand::thread_rng());

        let res =
            GraphEvaluator::<C1>::new(&Expression::Negated(Box::new(Expression::Constant(value))))
                .evaluate(&Mock::default(), 0);

        assert_eq!(res, -value);
    }

    #[traced_test]
    #[test]
    fn poly() {
        let mut rnd = rand::thread_rng();
        let [advice00, advice01, advice10, advice11, fixed00, fixed01, fixed10, fixed11] =
            array::from_fn(|_| Scalar::random(&mut rnd));
        let [selector1, selector2] = [true, false];

        let data = Mock {
            advice: vec![vec![advice00, advice10], vec![advice01, advice11]],
            fixed: vec![vec![fixed00, fixed10], vec![fixed01, fixed11]],
            selectors: vec![vec![selector1, selector2], vec![selector1, selector2]],
            ..Default::default()
        };

        let num_selectors = data.num_selectors();
        let num_fixed = data.num_fixed();

        let eval_selector = |column_index, rotation, row| {
            GraphEvaluator::<C1>::new(&Expression::Polynomial::<Scalar>(Query {
                index: column_index,
                rotation: Rotation(rotation),
            }))
            .evaluate(&data, row)
        };
        let eval_fixed = |column_index, rotation, row| {
            GraphEvaluator::<C1>::new(&Expression::Polynomial::<Scalar>(Query {
                index: num_selectors + column_index,
                rotation: Rotation(rotation),
            }))
            .evaluate(&data, row)
        };
        let eval_advice = |column_index, rotation, row| {
            GraphEvaluator::<C1>::new(&Expression::Polynomial::<Scalar>(Query {
                index: num_selectors + num_fixed + column_index,
                rotation: Rotation(rotation),
            }))
            .evaluate(&data, row)
        };

        assert_eq!(eval_advice(0, 0, 0), advice00);
        assert_eq!(eval_advice(0, 1, 0), advice10);
        assert_eq!(eval_advice(0, 0, 1), advice10);
        assert_eq!(eval_advice(0, -1, 1), advice00);
        assert_eq!(eval_advice(1, 0, 1), advice11);

        assert_eq!(eval_fixed(0, 0, 0), fixed00);
        assert_eq!(eval_fixed(0, 0, 1), fixed10);
        assert_eq!(eval_fixed(0, -1, 1), fixed00);

        assert_eq!(
            eval_selector(0, 0, 0),
            if selector1 { Scalar::ONE } else { Scalar::ZERO }
        );

        assert_eq!(
            eval_selector(0, 0, 1),
            if selector2 { Scalar::ONE } else { Scalar::ZERO }
        );
    }

    #[traced_test]
    #[test]
    fn challenge() {
        let value = Scalar::random(&mut rand::thread_rng());

        assert_eq!(
            GraphEvaluator::<C1>::new(&Expression::Challenge(0)).evaluate(
                &Mock {
                    challenges: vec![value],
                    ..Default::default()
                },
                0
            ),
            value
        );
    }

    #[traced_test]
    #[test]
    fn eval() {
        fn sum(expr: &[Expression<Scalar>]) -> Box<Expression<Scalar>> {
            Box::new(match expr.split_first() {
                Some((first, rest)) => Expression::Sum(Box::new(first.clone()), sum(rest)),
                None => Expression::Constant(Scalar::ZERO),
            })
        }

        let mut rnd = rand::thread_rng();
        let [advice00, advice01, advice10, advice11, fixed00, fixed01, fixed10, fixed11] =
            array::from_fn(|_| Scalar::random(&mut rnd));

        let data = Mock {
            advice: vec![vec![advice00, advice10], vec![advice01, advice11]],
            fixed: vec![vec![fixed00, fixed10], vec![fixed01, fixed11]],
            selectors: vec![vec![false; 2], vec![false; 2]],
            ..Default::default()
        };

        let num_selectors = data.num_selectors();
        let num_fixed = data.num_fixed();

        let get_fixed = |column_index, rotation| {
            Expression::Polynomial::<Scalar>(Query {
                index: num_selectors + column_index,
                rotation: Rotation(rotation),
            })
        };
        let get_advice = |column_index, rotation| {
            Expression::Polynomial::<Scalar>(Query {
                index: num_selectors + num_fixed + column_index,
                rotation: Rotation(rotation),
            })
        };

        assert_eq!(
            GraphEvaluator::<C1>::new(&Expression::Product(
                sum(&[get_advice(0, 0), get_advice(1, 0), get_advice(1, 0)]),
                sum(&[get_fixed(0, 0), get_advice(0, 0)]),
            ))
            .evaluate(&data, 0),
            (advice00 + advice01 + advice01) * (fixed00 + advice00)
        );
    }
}
