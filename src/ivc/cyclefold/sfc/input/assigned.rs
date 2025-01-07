use std::{fmt, iter};

use itertools::Itertools;
use tracing::{error, info, info_span, instrument, trace};

use crate::{
    gadgets::nonnative::bn::big_uint_mul_mod_chip::BigUintMulModChip,
    halo2_proofs::{
        circuit::Value,
        halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
        plonk::Error as Halo2PlonkError,
    },
    ivc::{
        self,
        cyclefold::{ro_chip, support_circuit, DEFAULT_LIMBS_COUNT, DEFAULT_LIMB_WIDTH},
    },
    main_gate::{self, AdviceCyclicAssignor, AssignedValue, MainGate, RegionCtx, WrapValue},
    poseidon::ROCircuitTrait,
};

pub type MainGateConfig = main_gate::MainGateConfig<{ super::super::MAIN_GATE_T }>;

pub type BigUint<F> = [F; DEFAULT_LIMBS_COUNT.get()];

pub type BigUintPoint<F> = ivc::protogalaxy::verify_chip::BigUintPoint<F>;
pub type NativePlonkInstance<F> = ivc::protogalaxy::verify_chip::AssignedPlonkInstance<F>;

const W_COMMITMENTS_MAX_LEN: usize = 3;
const W_CHALLENGES_MAX_LEN: usize = 3;

impl<F: PrimeField> NativePlonkInstance<F> {
    pub fn assign_advice_from_native(
        region: &mut RegionCtx<'_, F>,
        original: &super::NativePlonkInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let _s = info_span!("native_plonk_instance").entered();
        let start_offset = region.offset();

        trace!("start assign at {start_offset}");

        let super::NativePlonkInstance {
            W_commitments,
            instances,
            challenges,
        } = original;

        trace!(
            "W_commitments_len: {}, instances_len: {}, challenges_len: {}",
            W_commitments.len(),
            instances.len(),
            challenges.len()
        );

        let W_commitments = W_commitments
            .iter()
            .cloned()
            .map(|p| p.assign(region, main_gate_config))
            .collect::<Result<Vec<_>, _>>()?;

        iter::repeat(BigUintPoint::identity())
            .take(W_COMMITMENTS_MAX_LEN.saturating_sub(W_commitments.len()))
            .try_for_each(|p| p.assign(region, main_gate_config).map(|_| ()))?;

        let mut assigner = main_gate_config.advice_cycle_assigner();

        let instances = instances
            .iter()
            .map(|instance| {
                assigner.assign_all_advice(region, || "instance", instance.iter().cloned())
            })
            .collect::<Result<Vec<_>, _>>()?;

        let challenges =
            assigner.assign_all_advice(region, || "challenges", challenges.iter().cloned())?;

        assigner.assign_all_advice(
            region,
            || "zero",
            iter::repeat(F::ZERO).take(W_CHALLENGES_MAX_LEN.saturating_sub(challenges.len())),
        )?;

        trace!(
            "took {} rows total, finish at {}",
            region.offset() - start_offset,
            region.offset()
        );
        region.next();

        Ok(Self {
            W_commitments,
            instances,
            challenges,
        })
    }
}

pub type ProtoGalaxyAccumulatorInstance<F> =
    ivc::protogalaxy::verify_chip::AssignedAccumulatorInstance<F>;

impl<F: PrimeField> ProtoGalaxyAccumulatorInstance<F> {
    fn assign_advice_from_native(
        region: &mut RegionCtx<'_, F>,
        original: &super::ProtoGalaxyAccumulatorInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let _s = info_span!("protogalaxy_accumulator_instance").entered();
        let start_offset = region.offset();

        trace!("start assign at {start_offset}");

        let super::ProtoGalaxyAccumulatorInstance { ins, betas, e } = original;
        let ins = NativePlonkInstance::assign_advice_from_native(region, ins, main_gate_config)?;

        trace!("len of betas: {}", betas.len());
        let mut assigner = main_gate_config.advice_cycle_assigner();
        let self_ = Self {
            ins,
            betas: assigner
                .assign_all_advice(region, || "betas", betas.iter().cloned())?
                .into_boxed_slice(),
            e: assigner.assign_next_advice(region, || "e", *e)?,
        };

        trace!("took {} rows total", region.offset() - start_offset);
        region.next();

        Ok(self_)
    }

    pub fn conditional_select<const T: usize>(
        region: &mut RegionCtx<'_, F>,
        mg: &MainGate<F, T>,
        lhs: &Self,
        rhs: &Self,
        cond: &AssignedValue<F>,
    ) -> Result<Self, Halo2PlonkError> {
        let Self {
            ins: lhs_ins,
            betas: lhs_betas,
            e: lhs_e,
        } = lhs;

        let Self {
            ins: rhs_ins,
            betas: rhs_betas,
            e: rhs_e,
        } = rhs;

        Ok(Self {
            ins: NativePlonkInstance::conditional_select(region, mg, lhs_ins, rhs_ins, cond)?,
            betas: lhs_betas
                .iter()
                .zip_eq(rhs_betas)
                .map(|(l, r)| mg.conditional_select(region, l, r, cond))
                .collect::<Result<Vec<_>, _>>()?
                .into_boxed_slice(),
            e: mg.conditional_select(region, lhs_e, rhs_e, cond)?,
        })
    }
}

pub type ProtogalaxyProof<F> = ivc::protogalaxy::verify_chip::AssignedProof<F>;

impl<F: PrimeField> ProtogalaxyProof<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::nifs::protogalaxy::Proof<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let _s = info_span!("protogalaxy_proof").entered();
        let start_offset = region.offset();

        trace!("start assign at {start_offset}");

        let mut assigner = main_gate_config.advice_cycle_assigner();
        let super::nifs::protogalaxy::Proof { poly_F, poly_K } = original;

        trace!("poly_F_len: {}, poly_K_len: {}", poly_F.len(), poly_K.len());

        let self_ = Self {
            poly_F: assigner
                .assign_all_advice(region, || "poly_F", poly_F.iter().cloned())?
                .into(),
            poly_K: assigner
                .assign_all_advice(region, || "poly_K", poly_K.iter().cloned())?
                .into(),
        };

        trace!(
            "`ProtogalaxyProof` took {} rows",
            region.offset() - start_offset
        );
        region.next();

        Ok(self_)
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self { poly_F, poly_K } = self;

        poly_K
            .0
            .iter()
            .chain(poly_F.0.iter())
            .cloned()
            .map(WrapValue::Assigned)
    }
}

/// Recursive trace of the circuit itself
#[derive(Debug)]
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
        let start_offset = region.offset();
        let _s = info_span!("self_trace").entered();

        trace!("start assign at {start_offset}");

        let super::SelfTrace {
            input_accumulator,
            incoming,
            proof,
        } = original;

        let self_ = Self {
            input_accumulator: ProtoGalaxyAccumulatorInstance::assign_advice_from_native(
                region,
                input_accumulator,
                main_gate_config,
            )?,
            incoming: NativePlonkInstance::assign_advice_from_native(
                region,
                incoming,
                main_gate_config,
            )?,
            proof: ProtogalaxyProof::assign_advice_from(region, proof, main_gate_config)?,
        };

        trace!("`SelfTrace` took {} rows", region.offset() - start_offset);

        Ok(self_)
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

type BigUintView<F> = (AssignedValue<F>, BigUint<AssignedValue<F>>);

#[derive(Clone)]
pub struct PairedPlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<(AssignedValue<F>, AssignedValue<F>)>,
    pub(crate) instances: Vec<Vec<BigUintView<F>>>,
    pub(crate) challenges: Vec<BigUintView<F>>,
}

impl<F: PrimeField + fmt::Debug> fmt::Debug for PairedPlonkInstance<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[derive(Debug)]
        pub struct PairedPlonkInstanceValue<'l, F: PrimeField> {
            pub(crate) W_commitments: Vec<(Value<&'l F>, Value<&'l F>)>,
            pub(crate) instances: Vec<Vec<(Value<F>, BigUint<Value<F>>)>>,
            pub(crate) challenges: Vec<(Value<F>, BigUint<Value<F>>)>,
        }

        PairedPlonkInstanceValue {
            W_commitments: self
                .W_commitments
                .iter()
                .map(|(x, y)| (x.value(), y.value()))
                .collect(),
            instances: self
                .instances
                .iter()
                .map(|instance| {
                    instance
                        .iter()
                        .map(|(v, bn)| (v.value().copied(), bn.clone().map(|v| v.value().copied())))
                        .collect()
                })
                .collect(),
            challenges: self
                .challenges
                .iter()
                .map(|(cha, bn)| (cha.value().copied(), bn.clone().map(|v| v.value().copied())))
                .collect(),
        }
        .fmt(f)
    }
}

impl<F: PrimeField> PairedPlonkInstance<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::PairedPlonkInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let _s = info_span!("paired_plonk_instance").entered();
        let start_offset = region.offset();

        trace!("start assign at {}", start_offset);

        let super::PairedPlonkInstance {
            W_commitments,
            instances,
            challenges,
        } = original;

        let mut assigner = main_gate_config.advice_cycle_assigner();

        trace!("begin cycle is {}", region.offset());

        let W_commitments = W_commitments
            .iter()
            .map(|(x, y)| {
                let x_assigned = assigner.assign_next_advice(region, || "W_commitments_x", *x)?;
                let y_assigned = assigner.assign_next_advice(region, || "W_commitments_y", *y)?;
                Ok((x_assigned, y_assigned))
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        let _stock = iter::repeat((F::ZERO, F::ZERO))
            .take(W_COMMITMENTS_MAX_LEN - W_commitments.len())
            .try_for_each(|(x, y)| -> Result<(), Halo2PlonkError> {
                let _x = assigner.assign_next_advice(region, || "W_commitments_x", x)?;
                let _y = assigner.assign_next_advice(region, || "W_commitments_y", y)?;

                Ok(())
            });

        let instances = instances
            .iter()
            .map(|instance| {
                assigner.assign_all_advice(region, || "instance", instance.iter().copied())
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        let challenges =
            assigner.assign_all_advice(region, || "instance", challenges.iter().copied())?;

        assigner.assign_all_advice(
            region,
            || "",
            iter::repeat(F::ZERO).take(W_CHALLENGES_MAX_LEN - challenges.len()),
        )?;

        trace!("after cycle is {}", region.offset());
        region.next();

        let bn_chip = super::super::bn_chip(main_gate_config.clone());

        let instances: Vec<Vec<BigUintView<F>>> = instances
            .into_iter()
            .map(|instance| {
                instance
                    .into_iter()
                    .map(|value| {
                        Ok((
                            value.clone(),
                            bn_chip
                                .from_assigned_cell_to_limbs(region, &value)
                                .map_err(|err| {
                                    error!("bn error: {err:?}");
                                    Halo2PlonkError::Synthesis
                                })?
                                .try_into()
                                .unwrap(),
                        ))
                    })
                    .collect::<Result<Vec<_>, Halo2PlonkError>>()
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        let challenges = challenges
            .into_iter()
            .map(|value| {
                Ok((
                    value.clone(),
                    bn_chip
                        .from_assigned_cell_to_limbs(region, &value)
                        .map_err(|err| {
                            error!("bn error: {err:?}");
                            Halo2PlonkError::Synthesis
                        })?
                        .try_into()
                        .unwrap(),
                ))
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        trace!(
            "`PairedPlonkInstance` took {} rows",
            region.offset() - start_offset
        );

        Ok(Self {
            W_commitments,
            instances,
            challenges,
        })
    }

    pub fn conditional_select<const T: usize>(
        region: &mut RegionCtx<'_, F>,
        mg: &MainGate<F, T>,
        lhs: &Self,
        rhs: &Self,
        cond: &AssignedValue<F>,
    ) -> Result<Self, Halo2PlonkError> {
        let Self {
            W_commitments: lhs_W_commitments,
            instances: lhs_instances,
            challenges: lhs_challenges,
        } = lhs;
        let Self {
            W_commitments: rhs_W_commitments,
            instances: rhs_instances,
            challenges: rhs_challenges,
        } = rhs;

        let W_commitments = lhs_W_commitments
            .iter()
            .zip_eq(rhs_W_commitments.iter())
            .map(|((lx, ly), (rx, ry))| {
                Ok((
                    mg.conditional_select(region, lx, rx, cond)?,
                    mg.conditional_select(region, ly, ry, cond)?,
                ))
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        let instances = lhs_instances
            .iter()
            .zip_eq(rhs_instances.iter())
            .map(|(l_instance, r_instance)| {
                l_instance
                    .iter()
                    .zip_eq(r_instance.iter())
                    .map(|((l_val, l_bn), (r_val, r_bn))| {
                        let bn = l_bn
                            .iter()
                            .zip_eq(r_bn.iter())
                            .map(|(l, r)| mg.conditional_select(region, l, r, cond))
                            .collect::<Result<Vec<_>, _>>()?
                            .try_into()
                            .unwrap();

                        let val = mg.conditional_select(region, l_val, r_val, cond)?;

                        Ok((val, bn))
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?;

        let challenges = lhs_challenges
            .iter()
            .zip(rhs_challenges.iter())
            .map(|((l_val, l_bn), (r_val, r_bn))| {
                let bn = l_bn
                    .iter()
                    .zip_eq(r_bn.iter())
                    .map(|(l, r)| mg.conditional_select(region, l, r, cond))
                    .collect::<Result<Vec<_>, _>>()?
                    .try_into()
                    .unwrap();

                let val = mg.conditional_select(region, l_val, r_val, cond)?;

                Ok((val, bn))
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
                    .flat_map(|instance| instance.iter().map(|(value, _bn)| value)),
            )
            .chain(challenges.iter().map(|(value, _bn)| value))
            .map(|v| WrapValue::Assigned(v.clone()))
    }
}

#[derive(Clone, Debug)]
pub struct SangriaAccumulatorInstance<F: PrimeField> {
    pub(crate) ins: PairedPlonkInstance<F>,
    pub(crate) E_commitment: (AssignedValue<F>, AssignedValue<F>),
    pub(crate) u: AssignedValue<F>,
    // always zero for the support circuit
    pub(crate) step_circuit_instances_hash_accumulator: AssignedValue<F>,
}

impl<F: PrimeField> SangriaAccumulatorInstance<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::SangriaAccumulatorInstance<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let _s = info_span!("sangria_accumulator_instance").entered();

        let start_offset = region.offset();
        trace!("start assign at {}", region.offset());

        let ins = PairedPlonkInstance::assign_advice_from(region, &original.ins, main_gate_config)?;

        let mut assigner = main_gate_config.advice_cycle_assigner();

        let step_circuit_instances_hash_accumulator =
            assigner.assign_next_advice(region, || "", F::ZERO)?;

        let self_ = Self {
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
            u: assigner.assign_next_advice(region, || "u", original.u)?,
            step_circuit_instances_hash_accumulator,
        };

        trace!(
            "`SangriaAccumulatorInstance` took {} rows",
            region.offset() - start_offset
        );

        region.next();

        Ok(self_)
    }

    pub fn conditional_select<const T: usize>(
        region: &mut RegionCtx<'_, F>,
        mg: &MainGate<F, T>,
        lhs: &Self,
        rhs: &Self,
        cond: &AssignedValue<F>,
    ) -> Result<Self, Halo2PlonkError> {
        let Self {
            ins: lhs_ins,
            E_commitment: lhs_E_commitment,
            u: lhs_u,
            step_circuit_instances_hash_accumulator,
        } = lhs;
        let Self {
            ins: rhs_ins,
            E_commitment: rhs_E_commitment,
            u: rhs_u,
            step_circuit_instances_hash_accumulator: _,
        } = rhs;

        let ins = PairedPlonkInstance::conditional_select(region, mg, lhs_ins, rhs_ins, cond)?;

        let E_commitment = (
            mg.conditional_select(region, &lhs_E_commitment.0, &rhs_E_commitment.0, cond)?,
            mg.conditional_select(region, &lhs_E_commitment.1, &rhs_E_commitment.1, cond)?,
        );

        let u = mg.conditional_select(region, lhs_u, rhs_u, cond)?;

        Ok(Self {
            ins,
            E_commitment,
            u,
            step_circuit_instances_hash_accumulator: step_circuit_instances_hash_accumulator
                .clone(),
        })
    }

    fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            ins,
            E_commitment,
            u,
            step_circuit_instances_hash_accumulator,
        } = self;

        ins.iter_wrap_values().chain(
            [
                u.clone(),
                E_commitment.0.clone(),
                E_commitment.1.clone(),
                step_circuit_instances_hash_accumulator.clone(),
            ]
            .into_iter()
            .map(|v| WrapValue::Assigned(v)),
        )
    }
}

pub type SangriaCrossTermCommits<F> = Vec<(AssignedValue<F>, AssignedValue<F>)>;

#[derive(Debug)]
pub struct PairedIncoming<F: PrimeField> {
    pub instance: PairedPlonkInstance<F>,
    pub proof: SangriaCrossTermCommits<F>,
}

impl<F: PrimeField> PairedIncoming<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::PairedIncoming<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let start_offset = region.offset();

        let super::PairedIncoming { instance, proof } = original;

        let instance = PairedPlonkInstance::assign_advice_from(region, instance, main_gate_config)?;

        let mut assigner = main_gate_config.advice_cycle_assigner();

        let proof = proof
            .iter()
            .copied()
            .map(|(commit_x, commit_y)| -> Result<_, Halo2PlonkError> {
                Ok((
                    assigner.assign_next_advice(region, || "commit.x", commit_x)?,
                    assigner.assign_next_advice(region, || "commit.y", commit_y)?,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;

        trace!(
            "`PairedIncoming` took {} rows",
            region.offset() - start_offset
        );
        region.next();

        Ok(Self { instance, proof })
    }

    pub fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self { instance, proof } = self;
        instance
            .iter_wrap_values()
            .chain(proof.iter().flat_map(|(a, b)| {
                iter::once(WrapValue::Assigned(a.clone()))
                    .chain(std::iter::once(WrapValue::Assigned(b.clone())))
            }))
    }
}

#[derive(Debug)]
pub struct PairedTrace<F: PrimeField> {
    pub input_accumulator: SangriaAccumulatorInstance<F>,
    // The size from one to three
    // Depdend on `W_commitments_len`
    pub incoming: Box<[PairedIncoming<F>]>,
}

impl<F: PrimeField> PairedTrace<F> {
    fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::PairedTrace<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let _s = info_span!("paired_trace");

        trace!("start assign at {}", region.offset());

        let input_accumulator = SangriaAccumulatorInstance::assign_advice_from(
            region,
            &original.input_accumulator,
            main_gate_config,
        )?;

        let incoming = original
            .incoming
            .iter()
            .map(|paired_plonk_instance| {
                PairedIncoming::assign_advice_from(region, paired_plonk_instance, main_gate_config)
            })
            .collect::<Result<Vec<_>, Halo2PlonkError>>()?
            .into_boxed_slice();

        iter::repeat_with(|| &original.incoming[0])
            .take(W_COMMITMENTS_MAX_LEN - original.incoming.len())
            .try_for_each(|paired_plonk_instance| -> Result<(), Halo2PlonkError> {
                PairedIncoming::assign_advice_from(
                    region,
                    paired_plonk_instance,
                    main_gate_config,
                )?;
                Ok(())
            })?;

        Ok(Self {
            input_accumulator,
            incoming,
        })
    }

    pub fn iter_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            input_accumulator,
            incoming,
        } = self;

        input_accumulator.iter_wrap_values().chain(
            incoming
                .iter()
                .flat_map(|instance| instance.iter_wrap_values()),
        )
    }
}

#[derive(Debug)]
pub struct Input<const ARITY: usize, F: PrimeField> {
    pub pp_digest: (AssignedValue<F>, AssignedValue<F>),

    pub self_trace: SelfTrace<F>,
    pub paired_trace: PairedTrace<F>,

    pub step: AssignedValue<F>,
    pub z_0: [AssignedValue<F>; ARITY],
    pub z_i: [AssignedValue<F>; ARITY],
}

impl<const A: usize, F: PrimeField> Input<A, F> {
    pub fn assign_advice_from(
        region: &mut RegionCtx<'_, F>,
        original: &super::Input<A, F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError> {
        let _s = info_span!("input_assign").entered();

        let start_offset = region.offset();

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

        region.next();
        trace!("`Input` took {} rows", region.offset() - start_offset);

        Ok(Self {
            pp_digest: (pp_digest_0, pp_digest_1),
            self_trace,
            paired_trace,
            step: step_assigned,
            z_0: z_0.try_into().unwrap(),
            z_i: z_i.try_into().unwrap(),
        })
    }

    fn iter_consistency_marker_wrap_values(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
        let Self {
            self_trace,
            paired_trace,
            pp_digest: (pp0, pp1),
            step,
            z_0,
            z_i,
        } = self;

        iter_consistency_marker_wrap_values(
            (pp0, pp1),
            &self_trace.input_accumulator,
            &paired_trace.input_accumulator,
            step,
            z_0,
            z_i,
        )
    }

    pub fn consistency_check(
        self,
        region: &mut RegionCtx<F>,
        main_gate_config: &MainGateConfig,
    ) -> Result<Self, Halo2PlonkError>
    where
        F: PrimeFieldBits + FromUniformBytes<64>,
    {
        let mg = MainGate::new(main_gate_config.clone());

        let is_not_zero_term = mg.is_not_zero_term(region, self.step.clone())?;

        let calculated = ro_chip(main_gate_config.clone())
            .absorb_iter(self.iter_consistency_marker_wrap_values())
            .squeeze(region)?;

        let provided = self
            .self_trace
            .incoming
            .instances
            .first()
            .and_then(|instance| instance.first())
            .ok_or_else(|| {
                error!("No consistency marker in `incoming` trace");
                Halo2PlonkError::Synthesis
            })?;

        let calculated = mg.mul(region, &calculated, &is_not_zero_term)?;
        let provided = mg.mul(region, provided, &is_not_zero_term)?;

        region.constrain_equal(calculated.cell(), provided.cell())?;

        Ok(self)
    }

    #[instrument(skip_all)]
    pub fn pairing_check(
        &self,
        region: &mut RegionCtx<F>,
        main_gate_config: &MainGateConfig,
        poly_L_values: &[AssignedValue<F>],
        new_acc: &mut ProtoGalaxyAccumulatorInstance<F>,
    ) -> Result<(), Halo2PlonkError> {
        let bn_chip = BigUintMulModChip::new(
            main_gate_config.into_smaller_size().unwrap(),
            DEFAULT_LIMB_WIDTH,
            DEFAULT_LIMBS_COUNT,
        );

        let mg = MainGate::new(main_gate_config.clone());
        let is_zero_step = mg.is_zero_term(region, self.step.clone())?;

        let zero = region.assign_advice(|| "", main_gate_config.state[0], Value::known(F::ZERO))?;
        region.next();

        let expected_l0 = mg.conditional_select(region, &zero, &poly_L_values[0], &is_zero_step)?;
        let expected_l0_limbs = bn_chip
            .from_assigned_cell_to_limbs(region, &expected_l0)
            .map_err(|err| {
                error!("while make from L0 biguint form: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        let expected_l1 = mg.conditional_select(region, &zero, &poly_L_values[1], &is_zero_step)?;
        let expected_l1_limbs = bn_chip
            .from_assigned_cell_to_limbs(region, &expected_l1)
            .map_err(|err| {
                error!("while make from L1 biguint form: {err:?}");
                Halo2PlonkError::Synthesis
            })?;

        for (acc_W, incoming_W, trace, new_acc_W, index) in itertools::multizip((
            self.self_trace.input_accumulator.ins.W_commitments.iter(),
            self.self_trace.incoming.W_commitments.iter(),
            self.paired_trace.incoming.iter(),
            new_acc.ins.W_commitments.iter_mut(),
            0..,
        )) {
            info!("start {index} commitment check");

            let [expected_x, expected_y, x0, y0, l0, x1, y1, l1]: [_; support_circuit::INSTANCES_LEN] = trace.instance
                .instances
                .first()
                .expect("`SupportCircuit` always has instances.len() == 1 and it should always be used for sfc")
                .clone()
                .try_into()
                .unwrap();

            l0.1.iter()
                .zip_eq(expected_l0_limbs.iter())
                .enumerate()
                .try_for_each(|(i, (l, r))| {
                    if l.value() != r.value() {
                        error!("l0 limb[{i}] not equal: {:?} != {:?}", l.value(), r.value());
                    }
                    region.constrain_equal(l.cell(), r.cell())
                })?;

            l1.1.iter()
                .zip_eq(expected_l1_limbs.iter())
                .enumerate()
                .try_for_each(|(i, (l, r))| {
                    if l.value() != r.value() {
                        error!("l1 limb[{i}] not equal: {:?} != {:?}", l.value(), r.value());
                    }
                    region.constrain_equal(l.cell(), r.cell())
                })?;

            BigUintPoint::constrain_equal(region, acc_W, &BigUintPoint { x: x0.1, y: y0.1 })?;
            BigUintPoint::constrain_equal(region, incoming_W, &BigUintPoint { x: x1.1, y: y1.1 })?;

            *new_acc_W = BigUintPoint {
                x: expected_x.1,
                y: expected_y.1,
            };
        }

        Ok(())
    }
}

pub fn iter_consistency_marker_wrap_values<'l, const ARITY: usize, F: PrimeField>(
    pp_digest: (&'l AssignedValue<F>, &'l AssignedValue<F>),
    self_accumulator: &'l ProtoGalaxyAccumulatorInstance<F>,
    paried_accumulator: &'l SangriaAccumulatorInstance<F>,
    step: &'l AssignedValue<F>,
    z_0: &'l [AssignedValue<F>; ARITY],
    z_i: &'l [AssignedValue<F>; ARITY],
) -> impl 'l + Iterator<Item = WrapValue<F>> {
    let (pp0, pp1) = pp_digest;

    trace!(
        "oncircuit input protogalaxy accumulator: {:?}",
        self_accumulator
    );

    self_accumulator
        .iter_wrap_values()
        .chain(paried_accumulator.iter_wrap_values())
        .chain(
            [pp0, pp1, step]
                .into_iter()
                .chain(z_0.iter())
                .chain(z_i.iter())
                .map(|v| WrapValue::Assigned(v.clone())),
        )
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
                            .absorb_iter(assigned_input.iter_consistency_marker_wrap_values())
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
