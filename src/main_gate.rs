use halo2_proofs::arithmetic::CurveAffine;
use std::marker::PhantomData;
use halo2_proofs::{
    circuit::{AssignedCell, Chip, Cell, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Error}, 
    poly::Rotation};
use ff::PrimeField;
use crate::table::RelaxedPlonkInstance;

#[derive(Debug)]
pub struct RegionCtx<'a, F: PrimeField> {
    pub region: Region<'a, F>,
    pub offset: usize,
}

impl<'a, F:PrimeField> RegionCtx<'a, F> {
    pub fn new(region: Region<'a, F>, offset: usize) -> Self {
        RegionCtx {
            region,
            offset,
        }
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn into_region(self) -> Region<'a, F> {
        self.region
    }

     pub fn assign_fixed<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Fixed>,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region
            .assign_fixed(annotation, column, self.offset, || Value::known(value))
    }

    pub fn assign_advice<A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        self.region
            .assign_advice(annotation, column, self.offset, || value)
    }

    pub fn constrain_equal(&mut self, cell_0: Cell, cell_1: Cell) -> Result<(), Error> {
        self.region.constrain_equal(cell_0, cell_1)
    }

    pub fn next(&mut self) {
        self.offset += 1
    }

    pub(crate) fn reset(&mut self, offset: usize) {
        self.offset = offset
    }
}

pub enum WrapValue<F: PrimeField> {
    Assigned(AssignedCell<F, F>),
    Unassigned(Value<F>),
    Zero,
}

impl<F:PrimeField> From<Value<F>> for WrapValue<F> {
    fn from(val: Value<F>) -> Self {
        WrapValue::Unassigned(val)
    }
}

impl<F:PrimeField> From<AssignedCell<F, F>> for WrapValue<F> {
    fn from(val: AssignedCell<F, F>) -> Self {
        WrapValue::Assigned(val)
    }
}

impl<F:PrimeField> From<&AssignedCell<F, F>> for WrapValue<F> {
    fn from(val: &AssignedCell<F, F>) -> Self {
        WrapValue::Assigned(val.clone())
    }
}

pub struct AuxInput<C: CurveAffine> {
    i: C::Base,
    z0: Vec<C::Base>,
    zi: Option<Vec<C::Base>>,
    U: Option<RelaxedPlonkInstance<C>>,
    u: Option<RelaxedPlonkInstance<C>>,
}

#[derive(Clone, Debug)]
pub struct MainGateConfig<const T: usize> {
    pub(crate) state: [Column<Advice>; T],
    pub(crate) input: Column<Advice>,
    pub(crate) out: Column<Advice>,
    pub(crate) q_m: Column<Fixed>,
    // for linear term
    pub(crate) q_1: [Column<Fixed>; T],
    // for quintic term
    pub(crate) q_5: [Column<Fixed>; T],
    pub(crate) q_i: Column<Fixed>,
    pub(crate) q_o: Column<Fixed>,
    pub(crate) rc: Column<Fixed>,
}

#[derive(Debug)]
pub struct MainGate<F: PrimeField, const T: usize> {
    config: MainGateConfig<T>,
    _marker: PhantomData<F>
}

impl<F: PrimeField, const T: usize> Chip<F> for MainGate<F, T> {
    type Config = MainGateConfig<T>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}


impl<F: PrimeField, const T: usize> MainGate<F, T> {
    pub fn new(config: MainGateConfig<T>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: &mut (impl Iterator<Item = Column<Advice>> + Clone),
        fix_cols: &mut (impl Iterator<Item = Column<Fixed>> + Clone),
    ) -> MainGateConfig<T> {
        assert!(T>=2);
        let state = [0; T].map(|_| adv_cols.next().unwrap());
        let input = adv_cols.next().unwrap();
        let out = adv_cols.next().unwrap();
        let q_1 = [0; T].map(|_| fix_cols.next().unwrap());
        let q_5 = [0; T].map(|_| fix_cols.next().unwrap());
        let q_m = fix_cols.next().unwrap();
        let q_i = fix_cols.next().unwrap();
        let q_o = fix_cols.next().unwrap();
        let rc = fix_cols.next().unwrap();

        state.map(|s| {
            meta.enable_equality(s);
        });
        meta.enable_equality(out);

        let pow_5 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2 * v
        };

        meta.create_gate("q_m*s[0]*s[1] + sum_i(q_1[i]*s[i]) + sum_i(q_5[i]*s[i]^5) + rc + q_i*input + q_o*out=0", |meta|{
            let state = state.into_iter().map(|s| meta.query_advice(s, Rotation::cur())).collect::<Vec<_>>();
            let input = meta.query_advice(input, Rotation::cur());
            let out = meta.query_advice(out, Rotation::cur());
            let q_1 = q_1.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_5 = q_5.into_iter().map(|q| meta.query_fixed(q, Rotation::cur())).collect::<Vec<_>>();
            let q_m = meta.query_fixed(q_m, Rotation::cur());
            let q_i = meta.query_fixed(q_i, Rotation::cur());
            let q_o = meta.query_fixed(q_o, Rotation::cur());
            let rc = meta.query_fixed(rc, Rotation::cur());
            let init_term = q_m * state[0].clone() * state[1].clone() + q_i * input + rc + q_o * out;
            let res = state.into_iter().zip(q_1).zip(q_5).map(|((s, q1), q5)| {
                q1 * s.clone()  +  q5 * pow_5(s)
            }).fold(init_term, |acc, item| {
                acc + item
            });
            vec![res]
        });

        MainGateConfig {
            state,
            input,
            out,
            q_m,
            q_1,
            q_5,
            q_i,
            q_o,
            rc,
        }
    }

    // helper function for some usecases: no copy constraints, only return out cell
    // state: (q_1, q_m, state), out: (q_o, out)
    pub fn apply(&self, ctx: &mut RegionCtx<'_, F>, state: (Option<Vec<F>>, Option<F>, Option<Vec<WrapValue<F>>>), 
        rc: Option<F>, out: (F, WrapValue<F>)) -> Result<AssignedCell<F, F>, Error> {
        if let Some(q_1) = state.0 {
            for (i, val) in q_1.iter().enumerate() {
                ctx.assign_fixed(||"q_1", self.config.q_1[i], *val)?;
            }
        }
        if let Some(q_m_val) = state.1 {
            ctx.assign_fixed(||"q_m", self.config.q_m, q_m_val)?;
        }
        if let Some(state) = state.2 {
            for (i, val) in state.iter().enumerate() {
                match val {
                    WrapValue::Unassigned(vv) => {
                        ctx.assign_advice(||"state", self.config.state[i], *vv)?;
                    },
                    WrapValue::Assigned(avv) => {
                        let si = ctx.assign_advice(||"state", self.config.state[i], avv.value().copied())?;
                        ctx.constrain_equal(si.cell(), avv.cell())?;
                    },
                    _ => {},
                }
            }
        }

        if let Some(rc_val) = rc {
            ctx.assign_fixed(||"rc", self.config.rc, rc_val)?;
        }

        ctx.assign_fixed(||"q_o", self.config.q_o, out.0)?;

        let res = match out.1 {
            WrapValue::Unassigned(vv) => {
                ctx.assign_advice(||"out", self.config.out, vv)?
            },
            WrapValue::Assigned(avv) => {
                let out = ctx.assign_advice(||"out", self.config.out, avv.value().copied())?;
                ctx.constrain_equal(out.cell(), avv.cell())?;
                out
            },
            WrapValue::Zero => {
                unimplemented!() // this is not allowed
            },
        };
        ctx.next();
        Ok(res)
    }
                 

    // calculate sum_{i=0}^d r^i terms[i]
    pub fn random_linear_combination(&self, ctx: &mut RegionCtx<'_, F>, terms: Vec<F>, r: F) -> Result<AssignedCell<F,F>, Error> {
        let d = terms.len();
        let mut out: Option<AssignedCell<F,F>> = None;
        for i in 1..d {
            let lhs_val = Value::known(terms[d-1-i]);
            let rhs_val = if i == 1 {
                Value::known(terms[d-i])
            } else {
                out.as_ref().unwrap().value().copied()
            };
            let r_val = Value::known(r);
            ctx.assign_advice(||"input", self.config.input, lhs_val)?;
            let rhs = ctx.assign_advice(||"s[1]", self.config.state[1], rhs_val)?;
            if out.is_some() {
                ctx.constrain_equal(rhs.cell(), out.unwrap().cell())?;
            }
            ctx.assign_advice(||"s[0]", self.config.state[0], r_val)?;
            out = Some(ctx.assign_advice(||"out=s[0]*s[1]+input", self.config.out, lhs_val + r_val * rhs_val)?);

            ctx.assign_fixed(||"q_1[0]", self.config.q_1[0], F::ONE)?;
            ctx.assign_fixed(||"q_1[1]", self.config.q_1[1], F::ONE)?;
            ctx.assign_fixed(||"q_i", self.config.q_i, F::ONE)?;
            ctx.assign_fixed(||"q_m", self.config.q_m, F::ONE)?;
            ctx.assign_fixed(||"q_o", self.config.q_o, -F::ONE)?;
            ctx.next();
        }
        Ok(out.unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::Expression;
    // use pasta_curves::Fp;
    use halo2curves::pasta::Fp;

    fn main_gate_expressions() -> (Vec<Vec<Expression<Fp>>>,(usize,usize,usize)) {
        const T: usize = 2;
        const RATE: usize = 2;
        let mut cs = ConstraintSystem::<Fp>::default();
        let mut adv_cols = [(); T+2].map(|_| cs.advice_column()).into_iter();
        let mut fix_cols = [(); 2*T+4].map(|_| cs.fixed_column()).into_iter();
        let _: MainGateConfig<T> = MainGate::configure(&mut cs, &mut adv_cols, &mut fix_cols);
        let num_fixed = cs.num_fixed_columns();
        let num_instance = cs.num_instance_columns();
        let num_advice = cs.num_advice_columns();
        let gates: Vec<Vec<Expression<Fp>>> = cs.gates().iter().map(|gate| {
            gate.polynomials().iter().map(|expr| Expression::from_halo2_expr(expr, (num_fixed, num_instance))).collect()
        }).collect();
        (gates, (num_fixed, num_instance, num_advice))
    }

    #[test]
    fn test_main_gate_expr() {
        let (gates, _) = main_gate_expressions();
        for (i, gate) in gates.iter().enumerate() {
            for (j, poly) in gate.iter().enumerate() {
                if i == 0 && j == 0 {
                    // i.e. qm * s1_0 * s1_1 + qi * in1 + rc + qo * out1 + q1_0 * s1_0 + q5_0 * s1_0^5 
                    // + q1_1 * s1_1 + q5_1 * s1_1^5 
                    assert_eq!(format!("{}", poly), "(((((((Z_4 * Z_8) * Z_9) + (Z_5 * Z_10)) + Z_7) + (Z_6 * Z_11)) + ((Z_0 * Z_8) + (Z_2 * (((Z_8 * Z_8) * (Z_8 * Z_8)) * Z_8)))) + ((Z_1 * Z_9) + (Z_3 * (((Z_9 * Z_9) * (Z_9 * Z_9)) * Z_9))))");
                }
            }
        }
    }

    #[test]
    fn test_main_gate_cross_term() {
        let (gates, meta) = main_gate_expressions();
        let expr = gates[0][0].clone();
        let multipoly = expr.expand();
        let res = multipoly.fold_transform(meta);
        let r_index = meta.0 + 2*(meta.1+meta.2+1);
        let e1 = res.coeff_of((0, r_index), 0);
        let e2 = res.coeff_of((0, r_index), 5);
        // E1: (q5_0)(s1_0^5) + (q5_1)(s1_1^5) + (qm)(s1_0)(s1_1)(u1^3) + (q1_0)(s1_0)(u1^4) + (q1_1)(s1_1)(u1^4) + (qi)(in1)(u1^4) + (qo)(out1)(u1^4) + (rc)(u1^5)
        assert_eq!(format!("{}", e1), "(Z_2)(Z_8^5) + (Z_3)(Z_9^5) + (Z_4)(Z_8)(Z_9)(Z_12^3) + (Z_0)(Z_8)(Z_12^4) + (Z_1)(Z_9)(Z_12^4) + (Z_5)(Z_10)(Z_12^4) + (Z_6)(Z_11)(Z_12^4) + (Z_7)(Z_12^5)");
        // E2: (q5_0)(s2_0^5) + (q5_1)(s2_1^5) + (qm)(s2_0)(s2_1)(u2^3) + (q1_0)(s2_0)(u2^4) + (q1_1)(s2_1)(u2^4) + (qi)(in2)(u2^4) + (qo)(out2)(u2^4) + (rc)(u2^5)
        assert_eq!(format!("{}", e2), "(Z_2)(Z_13^5) + (Z_3)(Z_14^5) + (Z_4)(Z_13)(Z_14)(Z_17^3) + (Z_0)(Z_13)(Z_17^4) + (Z_1)(Z_14)(Z_17^4) + (Z_5)(Z_15)(Z_17^4) + (Z_6)(Z_16)(Z_17^4) + (Z_7)(Z_17^5)");
    }
}
