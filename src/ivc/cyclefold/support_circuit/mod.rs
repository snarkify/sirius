use std::{marker::PhantomData, num::NonZeroUsize};

use tracing::*;

use crate::{
    gadgets::ecc,
    halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        halo2curves::{
            ff::{PrimeField, PrimeFieldBits},
            CurveAffine,
        },
        plonk::{Circuit, Column, ConstraintSystem, Error as Halo2PlonkError, Instance},
    },
    ivc::cyclefold::support_circuit::ecc::AssignedPoint,
    main_gate::RegionCtx,
};

type EccChip<C> = ecc::EccChip<C, tiny_gate::Gate<<C as CurveAffine>::Base>>;

mod tiny_gate;
use tiny_gate::{Config as GateConfig, Gate};

#[derive(Default)]
pub struct SupportCircuit<C: CurveAffine> {
    _p: PhantomData<C>,
}

pub struct InstanceInput<C: CurveAffine> {
    pub p0: C,
    pub l0: C::Base,

    pub p1: C,
    pub l1: C::Base,

    pub p_out: C,
}

impl<C: CurveAffine> InstanceInput<C> {
    pub fn into_instance(self) -> Vec<Vec<C::Base>> {
        let p0 = self.p0.coordinates().unwrap();
        let p1 = self.p1.coordinates().unwrap();
        let p_out = self.p_out.coordinates().unwrap();

        vec![vec![
            *p_out.x(),
            *p_out.y(),
            *p0.x(),
            *p0.y(),
            self.l0,
            *p1.x(),
            *p1.y(),
            self.l1,
        ]]
    }
}

impl<C: CurveAffine> SupportCircuit<C> {
    pub const MIN_K_TABLE_SIZE: u32 = 15;
}

#[derive(Clone, Debug)]
pub struct Config {
    gate_config: GateConfig,
    instance: Column<Instance>,
}

impl<C: CurveAffine> Circuit<C::Base> for SupportCircuit<C>
where
    C::Base: PrimeFieldBits,
{
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        SupportCircuit { _p: PhantomData }
    }

    fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self::Config {
        let instance = meta.instance_column();
        meta.enable_equality(instance);

        Config {
            gate_config: Gate::configure(meta),
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Base>,
    ) -> Result<(), Halo2PlonkError> {
        let ecc_chip = EccChip::<C>::new(config.gate_config.clone());

        layouter.assign_region(
            || "",
            |region| {
                let mut ctx = RegionCtx::new(region, 0);

                let [expected_x, expected_y, x0, y0, l0, x1, y1, l1] = ecc_chip
                    .gate
                    .assign_values_from_instance(&mut ctx, config.instance, 0)
                    .unwrap();

                trace!("instances assigned");

                let [p0, p1] = [
                    AssignedPoint::<C> { x: x0, y: y0 },
                    AssignedPoint::<C> { x: x1, y: y1 },
                ];

                let num_bits =
                    NonZeroUsize::new(<C::Base as PrimeField>::NUM_BITS as usize).unwrap();

                let l0_bits = ecc_chip
                    .gate
                    .le_num_to_bits(&mut ctx, &l0, num_bits)
                    .unwrap();
                let lhs = ecc_chip
                    .scalar_mul_non_zero(&mut ctx, &p0, &l0_bits)
                    .unwrap();
                trace!("p0 * l0_bits = [{:?},{:?}]", lhs.x.value(), lhs.y.value());

                let l1_bits = ecc_chip
                    .gate
                    .le_num_to_bits(&mut ctx, &l1, num_bits)
                    .unwrap();
                trace!("l1 bits ready");
                let rhs = ecc_chip
                    .scalar_mul_non_zero(&mut ctx, &p1, &l1_bits)
                    .unwrap();
                trace!("p1 * l1_bits");

                let AssignedPoint {
                    x: actual_x,
                    y: actual_y,
                } = ecc_chip.add(&mut ctx, &lhs, &rhs).unwrap();
                trace!("add finished");

                ctx.constrain_equal(expected_x.cell(), actual_x.cell())
                    .unwrap();
                ctx.constrain_equal(expected_y.cell(), actual_y.cell())
                    .unwrap();

                Ok(())
            },
        )?;

        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use tracing_test::traced_test;

    use super::*;
    use crate::{
        gadgets::ecc::tests::Point,
        halo2_proofs::dev::MockProver,
        prelude::{bn256::C1Affine as Curve, Field},
    };

    type Base = <Curve as CurveAffine>::Base;
    type Scalar = <Curve as CurveAffine>::ScalarExt;

    #[traced_test]
    #[test]
    fn e2e() {
        let circuit = SupportCircuit::<Curve>::default();

        let mut rng = rand::thread_rng();
        let l0 = Scalar::random(&mut rng);
        let l1 = Scalar::random(&mut rng);

        let p0 = Curve::random(&mut rng);
        let p1 = Curve::random(&mut rng);

        let tmp = p0 * l0;
        trace!("p0 * l0_bits = {:?}", tmp);

        let p_out = Point::from(p0)
            .scalar_mul(&l0)
            .add(&Point::from(p1).scalar_mul(&l1))
            .into_curve();

        let l0 = Base::from_repr(l0.to_repr()).unwrap();
        let l1 = Base::from_repr(l1.to_repr()).unwrap();

        MockProver::run(
            SupportCircuit::<Curve>::MIN_K_TABLE_SIZE,
            &circuit,
            InstanceInput {
                p0,
                l0,
                p1,
                l1,
                p_out,
            }
            .into_instance(),
        )
        .unwrap()
        .verify()
        .unwrap();
    }
}
