use std::iter;

use halo2_proofs::halo2curves::ff::PrimeField;

use crate::{
    halo2_proofs::plonk::Error as Halo2PlonkError,
    main_gate::{self, AdviceCyclicAssignor, AssignedValue, RegionCtx, WrapValue},
};

pub type MainGateConfig = main_gate::MainGateConfig<{ super::super::T_MAIN_GATE }>;

type BigUint<F> = Vec<AssignedValue<F>>;

#[derive(Clone)]
pub struct BigUintPoint<F: PrimeField> {
    x_limbs: BigUint<F>,
    y_limbs: BigUint<F>,
}

impl<F: PrimeField> BigUintPoint<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::BigUintPoint<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let super::BigUintPoint { x, y } = original;
        let mut assigner = main_gate_config.advice_cycle_assigner();

        Ok(Self {
            x_limbs: assigner.assign_all_advice(region, || "x", x.limbs().iter().copied())?,
            y_limbs: assigner.assign_all_advice(region, || "y", y.limbs().iter().copied())?,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        self.x_limbs
            .iter()
            .chain(self.y_limbs.iter())
            .cloned()
            .map(|l| WrapValue::Assigned(l))
    }
}

#[derive(Clone)]
pub struct NativePlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<BigUintPoint<F>>,
    pub(crate) instances: Vec<Vec<AssignedValue<F>>>,
    pub(crate) challenges: Vec<AssignedValue<F>>,
}

impl<F: PrimeField> NativePlonkInstance<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::NativePlonkInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let super::NativePlonkInstance {
            W_commitments,
            instances,
            challenges,
        } = original;

        let W_commitments = W_commitments
            .iter()
            .map(|p| BigUintPoint::assign_advice_from(region, p, main_gate_config))
            .collect::<Result<Vec<_>, _>>()?;

        let mut assigner = main_gate_config.advice_cycle_assigner();

        let instances = instances
            .iter()
            .map(|instance| {
                assigner.assign_all_advice(region, || "instance", instance.iter().cloned())
            })
            .collect::<Result<Vec<_>, _>>()?;

        let challenges =
            assigner.assign_all_advice(region, || "challenges", challenges.iter().cloned())?;

        Ok(Self {
            W_commitments,
            instances,
            challenges,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            W_commitments,
            instances,
            challenges,
        } = self;

        W_commitments
            .iter()
            .flat_map(|W_commitment| W_commitment.iter_wrap_values())
            .chain(instances.iter().flat_map(|instance| {
                instance
                    .iter()
                    .map(|value| WrapValue::Assigned(value.clone()))
            }))
            .chain(
                challenges
                    .iter()
                    .map(|cha| WrapValue::Assigned(cha.clone())),
            )
    }
}

#[derive(Clone)]
pub struct ProtoGalaxyAccumulatorInstance<F: PrimeField> {
    pub(crate) ins: NativePlonkInstance<F>,
    pub(crate) betas: Box<[AssignedValue<F>]>,
    pub(crate) e: AssignedValue<F>,
}

impl<F: PrimeField> ProtoGalaxyAccumulatorInstance<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::ProtoGalaxyAccumulatorInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let super::ProtoGalaxyAccumulatorInstance { ins, betas, e } = original;
        let ins = NativePlonkInstance::assign_advice_from(region, ins, main_gate_config)?;

        let mut assigner = main_gate_config.advice_cycle_assigner();
        Ok(Self {
            ins,
            betas: assigner
                .assign_all_advice(region, || "betas", betas.iter().cloned())?
                .into_boxed_slice(),
            e: assigner.assign_next_advice(region, || "e", *e)?,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self { ins, betas, e } = self;
        ins.iter_wrap_values()
            .chain(betas.iter().cloned().map(WrapValue::Assigned))
            .chain(iter::once(WrapValue::Assigned(e.clone())))
    }
}

pub struct ProtogalaxyProof<F: PrimeField> {
    poly_F: Vec<AssignedValue<F>>,
    poly_K: Vec<AssignedValue<F>>,
}

impl<F: PrimeField> ProtogalaxyProof<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::nifs::protogalaxy::Proof<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let mut assigner = main_gate_config.advice_cycle_assigner();
        let super::nifs::protogalaxy::Proof { poly_F, poly_K } = original;

        Ok(Self {
            poly_F: assigner.assign_all_advice(region, || "poly_F", poly_F.iter().cloned())?,
            poly_K: assigner.assign_all_advice(region, || "poly_K", poly_K.iter().cloned())?,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self { poly_F, poly_K } = self;

        poly_K
            .iter()
            .chain(poly_F.iter())
            .cloned()
            .map(WrapValue::Assigned)
    }
}

/// Recursive trace of the circuit itself
pub struct SelfTrace<F: PrimeField> {
    pub input_accumulator: ProtoGalaxyAccumulatorInstance<F>,
    pub incoming: NativePlonkInstance<F>,
    pub proof: ProtogalaxyProof<F>,
}

impl<F: PrimeField> SelfTrace<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::SelfTrace<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let super::SelfTrace {
            input_accumulator,
            incoming,
            proof,
        } = original;

        Ok(Self {
            input_accumulator: ProtoGalaxyAccumulatorInstance::assign_advice_from(
                region,
                input_accumulator,
                main_gate_config,
            )?,
            incoming: NativePlonkInstance::assign_advice_from(region, incoming, main_gate_config)?,
            proof: ProtogalaxyProof::assign_advice_from(region, proof, main_gate_config)?,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            input_accumulator,
            incoming,
            proof,
        } = self;

        input_accumulator
            .iter_wrap_values()
            .chain(incoming.iter_wrap_values())
            .chain(proof.iter_wrap_values())
    }
}

#[derive(Clone)]
pub struct PairedPlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<(AssignedValue<F>, AssignedValue<F>)>,
    pub(crate) instances: Vec<Vec<BigUint<F>>>,
    pub(crate) challenges: Vec<BigUint<F>>,
}

impl<F: PrimeField> PairedPlonkInstance<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::PairedPlonkInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let super::PairedPlonkInstance {
            W_commitments,
            instances,
            challenges,
        } = original;
        let mut assigner = main_gate_config.advice_cycle_assigner();

        let W_commitments = W_commitments
            .iter()
            .map(|(x, y)| {
                let x_assigned = assigner.assign_next_advice(region, || "W_commitments_x", *x)?;
                let y_assigned = assigner.assign_next_advice(region, || "W_commitments_y", *y)?;
                Ok((x_assigned, y_assigned))
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        let instances = instances
            .iter()
            .map(|instance| {
                instance
                    .iter()
                    .map(|value| {
                        assigner.assign_all_advice(
                            region,
                            || "instances",
                            value.limbs().iter().copied(),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        let challenges = challenges
            .iter()
            .map(|challenge| {
                assigner.assign_all_advice(
                    region,
                    || "challenges",
                    challenge.limbs().iter().cloned(),
                )
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        Ok(Self {
            W_commitments,
            instances,
            challenges,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            W_commitments,
            instances,
            challenges,
        } = self;

        W_commitments
            .iter()
            .flat_map(|(x, y)| [x, y])
            .chain(
                instances
                    .iter()
                    .flat_map(|big_uint| big_uint.iter().flatten()),
            )
            .chain(challenges.iter().flat_map(|big_uint| big_uint.iter()))
            .map(|v| WrapValue::Assigned(v.clone()))
    }
}

pub struct SangriaAccumulatorInstance<F: PrimeField> {
    pub(crate) ins: PairedPlonkInstance<F>,
    pub(crate) E_commitment: (AssignedValue<F>, AssignedValue<F>),
    pub(crate) u: BigUint<F>,
}

impl<F: PrimeField> SangriaAccumulatorInstance<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::SangriaAccumulatorInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let ins = PairedPlonkInstance::assign_advice_from(region, &original.ins, main_gate_config)?;

        let mut assigner = main_gate_config.advice_cycle_assigner();

        Ok(Self {
            ins,
            E_commitment: (
                assigner.assign_next_advice(
                    region,
                    || "E_commitment_x",
                    original.E_commitment.0,
                )?,
                assigner.assign_next_advice(
                    region,
                    || "E_commitment_y",
                    original.E_commitment.1,
                )?,
            ),
            u: assigner.assign_all_advice(region, || "u", original.u.limbs().iter().cloned())?,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            ins,
            E_commitment,
            u,
        } = self;

        ins.iter_wrap_values().chain(
            [E_commitment.0.clone(), E_commitment.1.clone()]
                .into_iter()
                .chain(u.iter().cloned())
                .map(|v| WrapValue::Assigned(v)),
        )
    }
}

pub type SangriaCrossTermCommits<F> = Vec<(AssignedValue<F>, AssignedValue<F>)>;

pub struct PairedTrace<F: PrimeField> {
    pub input_accumulator: SangriaAccumulatorInstance<F>,
    // The size from one to three
    // Depdend on `W_commitments_len`
    pub incoming: Box<[PairedPlonkInstance<F>]>,
    proof: SangriaCrossTermCommits<F>,
}

impl<F: PrimeField> PairedTrace<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::PairedTrace<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let input_accumulator = SangriaAccumulatorInstance::assign_advice_from(
            region,
            &original.input_accumulator,
            main_gate_config,
        )?;

        let incoming = original
            .incoming
            .iter()
            .map(|paired_plonk_instance| {
                PairedPlonkInstance::assign_advice_from(
                    region,
                    paired_plonk_instance,
                    main_gate_config,
                )
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?
            .into_boxed_slice();

        let mut assigner = main_gate_config.advice_cycle_assigner();

        let proof = original
            .proof
            .iter()
            .map(|(a, b)| {
                Ok((
                    assigner.assign_next_advice(region, || "proof_a", *a)?,
                    assigner.assign_next_advice(region, || "proof_b", *b)?,
                ))
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        Ok(Self {
            input_accumulator,
            incoming,
            proof,
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            input_accumulator,
            incoming,
            proof,
        } = self;

        input_accumulator
            .iter_wrap_values()
            .chain(
                incoming
                    .iter()
                    .flat_map(|instance| instance.iter_wrap_values()),
            )
            .chain(proof.iter().flat_map(|(a, b)| {
                iter::once(WrapValue::Assigned(a.clone()))
                    .chain(std::iter::once(WrapValue::Assigned(b.clone())))
            }))
    }
}

pub struct Input<const ARITY: usize, F: PrimeField> {
    pub pp_digest: (AssignedValue<F>, AssignedValue<F>),

    pub self_trace: SelfTrace<F>,
    pub paired_trace: PairedTrace<F>,

    pub step: AssignedValue<F>,
    pub z_0: [AssignedValue<F>; ARITY],
    pub z_i: [AssignedValue<F>; ARITY],
}

impl<const A: usize, F: PrimeField> Input<A, F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::Input<A, F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let self_trace =
            SelfTrace::assign_advice_from(region, &original.self_trace, main_gate_config)?;

        let paired_trace =
            PairedTrace::assign_advice_from(region, &original.paired_trace, main_gate_config)?;

        let mut assigner = main_gate_config.advice_cycle_assigner();

        let pp_digest_0 =
            assigner.assign_next_advice(region, || "pp_digest_0", original.pp_digest.0)?;

        let pp_digest_1 =
            assigner.assign_next_advice(region, || "pp_digest_1", original.pp_digest.1)?;

        let step_assigned =
            assigner.assign_next_advice(region, || "step", F::from(original.step as u64))?;

        let z_0 = assigner.assign_all_advice(region, || "z_0", original.z_0.iter().cloned())?;

        let z_i = assigner.assign_all_advice(region, || "z_i", original.z_i.iter().cloned())?;

        Ok(Self {
            pp_digest: (pp_digest_0, pp_digest_1),
            self_trace,
            paired_trace,
            step: step_assigned,
            z_0: z_0.try_into().unwrap(),
            z_i: z_i.try_into().unwrap(),
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            self_trace,
            paired_trace,
            pp_digest: (pp0, pp1),
            step,
            z_0,
            z_i,
        } = self;

        self_trace
            .input_accumulator
            .iter_wrap_values()
            .chain(paired_trace.input_accumulator.iter_wrap_values())
            .chain(
                [pp0, pp1, step]
                    .into_iter()
                    .chain(z_0.iter())
                    .chain(z_i.iter())
                    .map(|v| WrapValue::Assigned(v.clone())),
            )
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use halo2_proofs::{
        halo2curves::ff::{FromUniformBytes, PrimeFieldBits},
        plonk::{Column, Instance},
    };
    use tracing_test::traced_test;

    use super::{super::Input, Input as AssignedInput, MainGateConfig};
    use crate::{
        halo2_proofs::{
            circuit::SimpleFloorPlanner,
            dev::MockProver,
            halo2curves::{ff::PrimeField, pasta::Fq},
            plonk::{Circuit, Error as Halo2PlonkError},
        },
        ivc::cyclefold::{ro, ro_chip},
        main_gate::{MainGate, RegionCtx},
        poseidon::{ROCircuitTrait, ROTrait},
    };

    #[traced_test]
    #[test]
    fn consistency() {
        struct Test<F: PrimeField>(Input<2, F>);

        #[derive(Clone, Debug)]
        struct Config {
            mg: MainGateConfig,
            io: Column<Instance>,
        }

        impl<F: PrimeFieldBits + FromUniformBytes<64>> Circuit<F> for Test<F> {
            type Config = Config;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                todo!()
            }

            fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
                let mg = MainGate::configure(meta);
                let io = meta.instance_column();
                meta.enable_equality(io);

                Self::Config { mg, io }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl halo2_proofs::circuit::Layouter<F>,
            ) -> Result<(), Halo2PlonkError> {
                let input = self.0.clone();

                let outpuot = layouter.assign_region(
                    || "main",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);
                        let assigned_input =
                            AssignedInput::assign_advice_from(&mut region, &input, &config.mg)?;

                        let mut ro = ro_chip::<F>(config.mg.clone());
                        let output = ro
                            .absorb_iter(assigned_input.iter_wrap_values())
                            .squeeze(&mut region)?;

                        Ok(output)
                    },
                )?;

                layouter.constrain_instance(outpuot.cell(), config.io, 0)?;

                Ok(())
            }
        }

        let input = Input::random(&mut rand::thread_rng());

        let expected = ro()
            .absorb(&input)
            .output(NonZeroUsize::new(Fq::NUM_BITS as usize).unwrap());

        MockProver::<Fq>::run(16, &Test(input), vec![vec![expected]])
            .unwrap()
            .verify()
            .unwrap();
    }
}
