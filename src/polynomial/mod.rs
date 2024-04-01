pub mod expression;
pub mod grouped_poly;
pub mod monomial;
pub mod multi_polynomial;
pub mod sparse;

pub use expression::{ColumnIndex, Expression, Query};
pub use monomial::Monomial;
pub use multi_polynomial::MultiPolynomial;

pub mod graph_evaluator {
    use ff::{Field, PrimeField};
    use halo2_proofs::poly::Rotation;
    use halo2curves::CurveAffine;

    use crate::plonk::eval::Eval;

    use super::Expression;

    /// Return the index in the polynomial of size `isize` after rotation `rot`.
    fn get_rotation_idx(idx: usize, rot: i32, rot_scale: i32, isize: i32) -> usize {
        (((idx as i32) + (rot * rot_scale)).rem_euclid(isize)) as usize
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
        Advice(usize, usize),
        /// This is an instance (external) column
        Instance(usize, usize),
        /// This is a challenge
        Challenge(usize),
        /// Previous value
        PreviousValue(),
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
            _rotations: &[usize],
            constants: &[F],
            intermediates: &[F],
            _eval_getter: &impl Eval<F>,
            _previous_value: &F,
        ) -> F {
            let get_value = |value: &ValueSource| -> F {
                match value {
                    ValueSource::Constant(id) => constants[*id],
                    ValueSource::Intermediate(id) => intermediates[*id],
                    ValueSource::Fixed { index, rotation } => todo!("{index}{rotation}"),
                    ValueSource::Advice(_, _) => todo!(),
                    ValueSource::Instance(_, _) => todo!(),
                    ValueSource::Challenge(_) => todo!(),
                    ValueSource::PreviousValue() => todo!(),
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
        pub constants: Vec<C::ScalarExt>,
        /// Rotations
        pub rotations: Vec<i32>,
        /// Calculations
        pub calculations: Vec<CalculationInfo>,
        /// Number of intermediates
        pub num_intermediates: usize,
    }

    impl<C: CurveAffine> GraphEvaluator<C> {
        /// Adds a rotation
        fn add_rotation(&mut self, rotation: &Rotation) -> usize {
            let position = self.rotations.iter().position(|&c| c == rotation.0);
            match position {
                Some(pos) => pos,
                None => {
                    self.rotations.push(rotation.0);
                    self.rotations.len() - 1
                }
            }
        }

        /// Adds a constant
        fn add_constant(&mut self, constant: &C::ScalarExt) -> ValueSource {
            let position = self.constants.iter().position(|&c| c == *constant);
            ValueSource::Constant(match position {
                Some(pos) => pos,
                None => {
                    self.constants.push(*constant);
                    self.constants.len() - 1
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
                Some(existing_calculation) => {
                    ValueSource::Intermediate(existing_calculation.target)
                }
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
                    self.add_calculation(Calculation::Store(ValueSource::Advice(
                        query.index,
                        rot_idx,
                    )))
                }
                Expression::Challenge(challenge_index) => self
                    .add_calculation(Calculation::Store(ValueSource::Challenge(*challenge_index))),
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
                            let result_a = self.add_expression(a);
                            let result_b = self.add_expression(b);
                            if result_a == ValueSource::Constant(0) {
                                result_b
                            } else if result_b == ValueSource::Constant(0) {
                                result_a
                            } else if result_a <= result_b {
                                self.add_calculation(Calculation::Add(result_a, result_b))
                            } else {
                                self.add_calculation(Calculation::Add(result_b, result_a))
                            }
                        }
                    }
                }
                Expression::Product(a, b) => {
                    let result_a = self.add_expression(a);
                    let result_b = self.add_expression(b);
                    if result_a == ValueSource::Constant(0) || result_b == ValueSource::Constant(0)
                    {
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

        pub fn evaluate(
            &self,
            data: &mut EvaluationData<C>,
            getter: &impl Eval<C::ScalarExt>,
            previous_value: &C::ScalarExt,
            idx: usize,
            rot_scale: i32,
            isize: i32,
        ) -> C::ScalarExt {
            // All rotation index values
            for (rot_idx, rot) in self.rotations.iter().enumerate() {
                data.rotations[rot_idx] = get_rotation_idx(idx, *rot, rot_scale, isize);
            }

            // All calculations, with cached intermediate results
            for calc in self.calculations.iter() {
                data.intermediates[calc.target] = calc.calculation.evaluate(
                    &data.rotations,
                    &self.constants,
                    &data.intermediates,
                    getter,
                    previous_value,
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
}
