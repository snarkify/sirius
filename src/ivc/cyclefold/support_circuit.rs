use std::marker::PhantomData;

use crate::{
    constants::NUM_CHALLENGE_BITS,
    gadgets::ecc,
    halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{Circuit, ConstraintSystem, Error as Halo2PlonkError},
    },
    ivc::cyclefold::support_circuit::ecc::AssignedPoint,
    main_gate::RegionCtx,
};

type EccChip<C> = ecc::EccChip<C, tiny_gate::Gate<<C as CurveAffine>::Base>>;

mod tiny_gate;
use halo2_proofs::halo2curves::{ff::PrimeFieldBits, CurveAffine};
use tiny_gate::{Config as GateConfig, Gate};

use crate::halo2_proofs::plonk::{Column, Instance};

pub struct SupportCircuit<C: CurveAffine> {
    _p: PhantomData<C>,
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

                let [x0, y0, l0, x1, y1, l1, expected_x, expected_y] = ecc_chip
                    .gate
                    .assign_values_from_instance(&mut ctx, config.instance, 0)?;
                let [p0, p1] = [
                    AssignedPoint::<C> { x: x0, y: y0 },
                    AssignedPoint::<C> { x: x1, y: y1 },
                ];

                let l0_bits = ecc_chip
                    .gate
                    .le_num_to_bits(&mut ctx, l0, NUM_CHALLENGE_BITS)?;
                let lhs = ecc_chip.scalar_mul_non_zero(&mut ctx, &p0, &l0_bits)?;

                let l1_bits = ecc_chip
                    .gate
                    .le_num_to_bits(&mut ctx, l1, NUM_CHALLENGE_BITS)?;
                let rhs = ecc_chip.scalar_mul_non_zero(&mut ctx, &p1, &l1_bits)?;

                let AssignedPoint {
                    x: actual_x,
                    y: actual_y,
                } = ecc_chip.add(&mut ctx, &lhs, &rhs)?;

                ctx.constrain_equal(expected_x.cell(), actual_x.cell())?;
                ctx.constrain_equal(expected_y.cell(), actual_y.cell())?;

                Ok(())
            },
        )?;

        Ok(())
    }
}
