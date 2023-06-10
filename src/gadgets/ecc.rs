use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::{Chip, Value},
    plonk::Error,
};
use ff::Field;
use crate::{
    main_gate::{RegionCtx, MainGate, MainGateConfig},
    gadgets::AssignedValue,
};

// assume point is not infinity 
#[derive(Clone)]
pub struct AssignedPoint<C: CurveAffine> {
    pub(crate) x: AssignedValue<C::Base>,
    pub(crate) y: AssignedValue<C::Base>,
}

impl<C: CurveAffine> AssignedPoint<C> {

    pub fn coordinates(&self) -> (&AssignedValue<C::Base>, &AssignedValue<C::Base>) {
        (&self.x, &self.y)
    }


}

pub struct EccChip<C: CurveAffine, const T: usize> {
    main_gate: MainGate<C::Base, T>,
}

impl<C: CurveAffine, const T: usize> EccChip<C, T> {
    pub fn new(config: MainGateConfig<T>) -> Self {
        let main_gate =  MainGate::new(config);
        Self {
            main_gate,
        }
    }

    pub fn assign_point(&self, ctx: &mut RegionCtx<'_, C::Base>, coords: Option<(C::Base, C::Base)>) -> Result<AssignedPoint<C>, Error> {
        let x = ctx.assign_advice(||"x", self.main_gate.config().state[0], Value::known(coords.map_or(C::Base::ZERO,|c|c.0)))?;
        let y = ctx.assign_advice(||"y", self.main_gate.config().state[1], Value::known(coords.map_or(C::Base::ZERO, |c|c.1)))?;
        ctx.next();

        Ok(AssignedPoint {
            x,
            y,
        })
    }

    pub fn add(&self, ctx: &mut RegionCtx<'_, C::Base>, p: &AssignedPoint<C>, q: &AssignedPoint<C>) -> Result<AssignedPoint<C>, Error> {
        let is_p_iden = self.main_gate.is_infinity_point(ctx, &p.x, &p.y)?;
        let is_q_iden = self.main_gate.is_infinity_point(ctx, &q.x, &q.y)?;
        let is_equal_x = self.main_gate.is_equal_term(ctx, &p.x, &q.x)?;
        let is_equal_y = self.main_gate.is_equal_term(ctx, &p.y, &q.y)?;

        let inf = self.assign_point(ctx, None)?;
        let r  = self._add_unsafe(ctx, p, q)?;
        let p2 = self.double(ctx, p)?;

        let x1 = self.main_gate.conditional_select(ctx, &p2.x, &inf.x, &is_equal_y)?;
        let y1 = self.main_gate.conditional_select(ctx, &p2.y, &inf.y, &is_equal_y)?;
        let x2 = self.main_gate.conditional_select(ctx, &x1, &r.x, &is_equal_x)?;
        let y2 = self.main_gate.conditional_select(ctx, &y1, &r.y, &is_equal_x)?;
        let x3 = self.main_gate.conditional_select(ctx, &p.x, &x2, &is_q_iden)?;
        let y3 = self.main_gate.conditional_select(ctx, &p.y, &y2, &is_q_iden)?;
        let x = self.main_gate.conditional_select(ctx, &q.x, &x3, &is_p_iden)?;
        let y = self.main_gate.conditional_select(ctx, &q.y, &y3, &is_p_iden)?;

        Ok(AssignedPoint{x, y})
    }

    fn _add_unsafe(&self, ctx: &mut RegionCtx<'_, C::Base>, p: &AssignedPoint<C>, q: &AssignedPoint<C>) -> Result<AssignedPoint<C>, Error> {
        let yd = self.main_gate.sub(ctx, &p.y, &q.y)?;
        let xd = self.main_gate.sub(ctx, &p.x, &q.x)?;
        let lambda = self.main_gate.divide(ctx, &yd, &xd)?;
        let lambda2 = self.main_gate.square(ctx, &lambda)?;
        let tmp1 = self.main_gate.sub(ctx, &lambda2, &p.x)?;
        let xr = self.main_gate.sub(ctx, &tmp1, &q.x)?;
        let tmp2 = self.main_gate.sub(ctx, &p.x, &xr)?;
        let tmp3 = self.main_gate.mul(ctx, &lambda, &tmp2)?;
        let yr = self.main_gate.sub(ctx, &tmp3, &p.y)?;
        Ok(AssignedPoint {
            x: xr,
            y: yr,
        })
    }

    fn double(&self, ctx: &mut RegionCtx<'_, C::Base>, p: &AssignedPoint<C>) -> Result<AssignedPoint<C>, Error> {
        let is_inf = self.main_gate.is_infinity_point(ctx, &p.x, &p.y)?;
        let inf = self.assign_point(ctx, None)?;
        let p2 = self._double_unsafe(ctx, p)?;

        let x = self.main_gate.conditional_select(ctx, &inf.x, &p2.x, &is_inf)?;
        let y = self.main_gate.conditional_select(ctx, &inf.y, &p2.y, &is_inf)?;
        Ok(AssignedPoint{x, y})
    }

    // assume a = 0 in weierstrass curve y^2 = x^3 + ax + b
    fn _double_unsafe(&self, ctx: &mut RegionCtx<'_, C::Base>, p: &AssignedPoint<C>) -> Result<AssignedPoint<C>, Error> {
        let xp2 = self.main_gate.square(ctx, &p.x)?;
        let lnum = self.main_gate.mul_by_const(ctx, &xp2, C::Base::from(3))?;
        let lden = self.main_gate.add(ctx, &p.y, &p.y)?;
        let lambda = self.main_gate.divide(ctx, &lnum, &lden)?;
        let lambda2 = self.main_gate.square(ctx, &lambda)?;

        let tmp1 = self.main_gate.sub(ctx, &lambda2, &p.x)?;
        let xr = self.main_gate.sub(ctx, &tmp1, &p.x)?;
        let tmp2 = self.main_gate.sub(ctx, &p.x, &xr)?;
        let tmp3 = self.main_gate.mul(ctx, &lambda, &tmp2)?;
        let yr = self.main_gate.sub(ctx, &tmp3, &p.y)?;
        Ok(AssignedPoint {
            x: xr,
            y: yr,
        })
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::poly::ipa::commitment::{IPACommitmentScheme, ParamsIPA};
    use halo2_proofs::poly::ipa::multiopen::ProverIPA;
    use halo2_proofs::poly::{VerificationStrategy, ipa::strategy::SingleStrategy};
    use halo2_proofs::poly::commitment::ParamsProver;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer};
    use halo2_proofs::plonk::{ConstraintSystem, Column, Circuit, Instance, create_proof, keygen_pk, keygen_vk, verify_proof};
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2curves::pasta::{pallas, vesta, EqAffine, Fp};
    use ff::PrimeFieldBits;
    use rand_core::OsRng;

    #[derive(Clone, Debug)]
    struct Point<C: CurveAffine> {
        x: C::Base,
        y: C::Base,
        is_inf: bool,
    }
    impl<C: CurveAffine> Point<C> {
        fn default() -> Self {
            Self {
                x: C::Base::ZERO,
                y: C::Base::ZERO,
                is_inf: true
            }
        }

         /// Add any two points
        pub fn add(&self, other: &Point<C>) -> Self {
          if self.x == other.x {
            // If self == other then call double
            if self.y == other.y {
              self.double()
            } else {
              // if self.x == other.x and self.y != other.y then return infinity
              Self {
                x: C::Base::ZERO,
                y: C::Base::ZERO,
                is_inf: true,
              }
            }
          } else {
            self.add_internal(other)
          }
        }
    
        /// Add two different points
        pub fn add_internal(&self, other: &Point<C>) -> Self {
          if self.is_inf {
            return other.clone();
          }
    
          if other.is_inf {
            return self.clone();
          }
    
          let lambda = (other.y - self.y) * (other.x - self.x).invert().unwrap();
          let x = lambda * lambda - self.x - other.x;
          let y = lambda * (self.x - x) - self.y;
          Self {
            x,
            y,
            is_inf: false,
          }
        }

        pub fn double(&self) -> Self {
          if self.is_inf {
            return Self {
              x: C::Base::ZERO,
              y: C::Base::ZERO,
              is_inf: true,
            };
          }
    
          let lambda = C::Base::from(3)
            * self.x
            * self.x
            * ((C::Base::ONE + C::Base::ONE) * self.y).invert().unwrap();
          let x = lambda * lambda - self.x - self.x;
          let y = lambda * (self.x - x) - self.y;
          Self {
            x,
            y,
            is_inf: false,
          }
        }

        fn scalar_mul<F: PrimeFieldBits> (&self, scalar: &F) -> Self {
          let mut res = Self {
            x: C::Base::ZERO,
            y: C::Base::ZERO,
            is_inf: true,
          };
    
          let bits = scalar.to_le_bits();
          for i in (0..bits.len()).rev() {
            res = res.double();
            if bits[i] {
              res = self.add(&res);
            }
          }
          res
        }

        fn random_vartime() -> Self {
          loop {
            let x = C::Base::random(&mut OsRng);
            let y = (x.square() * x + C::b()).sqrt();
            if y.is_some().unwrap_u8() == 1 {
              return Self {
                x,
                y: y.unwrap(),
                is_inf: false,
              };
            }
          }
        }
    }

    const T: usize = 4;
    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
       config: MainGateConfig<T>,
       instance: Column<Instance>
    }

    struct TestCircuit<C: CurveAffine> {
        a: Point<C>,
        b: Point<C>,
        test_case: usize, // 0: add, 1: double
    }
    impl<C: CurveAffine> TestCircuit<C> {
        fn new(a: Point<C>, b: Point<C>, test_case: usize) -> Self {
            Self {
                a,
                b,
                test_case,
            }
        }
    }

    impl<C: CurveAffine> Circuit<C::Base> for TestCircuit<C> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;


        fn without_witnesses(&self) -> Self {
            TestCircuit::new(Point::default(), Point::default(), 0)
        }

        fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let mut adv_cols = [(); T+2].map(|_| meta.advice_column()).into_iter();
            let mut fix_cols = [(); 2*T+4].map(|_| meta.fixed_column()).into_iter();
            let config = MainGate::configure(meta, &mut adv_cols, &mut fix_cols);
            Self::Config {
                config,
                instance,
            }
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<C::Base>) -> Result<(), Error> {
             let ecc_chip = EccChip::<C, T>::new(config.config);
             let output = layouter.assign_region(||"poseidon hash", |region|{
                 let ctx = &mut RegionCtx::new(region, 0);
                 let ax = ctx.assign_advice(||"a.x", ecc_chip.main_gate.config().state[0], Value::known(self.a.x))?;
                 let ay = ctx.assign_advice(||"a.y", ecc_chip.main_gate.config().state[1], Value::known(self.a.y))?;
                 ctx.next();
                 let a = AssignedPoint { x: ax, y: ay };
                 let output = if self.test_case == 0 {
                     let bx = ctx.assign_advice(||"b.x", ecc_chip.main_gate.config().state[2], Value::known(self.b.x))?;
                     let by = ctx.assign_advice(||"b.y", ecc_chip.main_gate.config().state[3], Value::known(self.b.y))?;
                     ctx.next();
                     let b = AssignedPoint { x: bx, y: by };
                     ecc_chip.add(ctx, &a, &b)
                 } else {
                     ecc_chip.double(ctx, &a)
                 };
                 ctx.next();
                 output
             })?;
             layouter.constrain_instance(output.x.cell(), config.instance, 0)?;
             layouter.constrain_instance(output.y.cell(), config.instance, 1)?;
             Ok(())
        }
    }

    #[test]
    fn test_ecc_double() {
        println!("-----running ECC Circuit-----");
        let K:u32 = 8;
        type Scheme = IPACommitmentScheme<EqAffine>;
        let params: ParamsIPA<vesta::Affine> = ParamsIPA::<EqAffine>::new(K);
        let p: Point<pallas::Affine> = Point::random_vartime();
        let q: Point<pallas::Affine> = Point { x: Fp::ZERO, y: Fp::ZERO, is_inf: true };
        //let q: Point<pallas::Affine> = Point { x: p.x, y: -p.y, is_inf: false };
        let r = p.add(&q);
        let circuit = TestCircuit::new(p, q, 0);

        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
        let public_inputs: &[&[Fp]] = &[&[r.x, r.y]];
        let mut transcript = Blake2bWrite::<_, EqAffine, Challenge255<_>>::init(vec![]);
        create_proof::<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>(&params, &pk, &[circuit], &[public_inputs], OsRng, &mut transcript)
              .expect("proof generation should not fail");

        let proof = transcript.finalize();
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&params);
        verify_proof(&params, pk.get_vk(), strategy, &[public_inputs], &mut transcript).unwrap();
        println!("-----ecc add works fine-----");
    }

    #[test] 
    fn test_mock_add() {
        use halo2_proofs::dev::MockProver;
        let K:u32 = 8;
        let p: Point<pallas::Affine> = Point::random_vartime();
        let q: Point<pallas::Affine> = Point::random_vartime();
        let r = p.add(&q);
        let circuit = TestCircuit::new(p, q, 0);
        let public_inputs = vec![vec![r.x, r.y]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
