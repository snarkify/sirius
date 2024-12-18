use itertools::Itertools;
use num_traits::Num;
use tracing::error;

use super::{input, MAIN_GATE_T};
use crate::{
    constants::MAX_BITS,
    gadgets::{
        ecc::{AssignedPoint, EccChip},
        nonnative::{self, bn::big_uint_mul_mod_chip::BigUintMulModChip},
    },
    halo2_proofs::{
        halo2curves::{
            ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
            CurveAffine,
        },
        plonk::Error as Halo2PlonkError,
    },
    ivc::{
        cyclefold::{ro_chip, DEFAULT_LIMBS_COUNT_LIMIT, DEFAULT_LIMB_WIDTH},
        fold_relaxed_plonk_instance_chip::{self, BigUintView, FoldRelaxedPlonkInstanceChip},
    },
    main_gate::{MainGate, MainGateConfig, RegionCtx},
    nifs::sangria,
    poseidon::ROCircuitTrait,
};

fn bn_chip<F: PrimeField>(main_gate_config: MainGateConfig<MAIN_GATE_T>) -> BigUintMulModChip<F> {
    BigUintMulModChip::new(
        main_gate_config.into_smaller_size().unwrap(),
        DEFAULT_LIMB_WIDTH,
        DEFAULT_LIMBS_COUNT_LIMIT,
    )
}

fn ecc_chip<CSup: CurveAffine>(
    main_gate_config: MainGateConfig<MAIN_GATE_T>,
) -> EccChip<CSup, MainGate<CSup::Base, MAIN_GATE_T>> {
    EccChip::new(main_gate_config.into_smaller_size().unwrap())
}

use nonnative::bn::big_uint::{self, BigUint};

fn module_as_bn<F1: PrimeField, F2: PrimeField>() -> Result<BigUint<F1>, big_uint::Error> {
    BigUint::<F1>::from_biguint(
        &num_bigint::BigUint::from_str_radix(
            <F2 as PrimeField>::MODULUS.trim_start_matches("0x"),
            16,
        )
        .unwrap(),
        DEFAULT_LIMB_WIDTH,
        DEFAULT_LIMBS_COUNT_LIMIT,
    )
}

pub fn fold<CMain: CurveAffine, CSup: CurveAffine<Base = CMain::ScalarExt>>(
    region: &mut RegionCtx<CMain::ScalarExt>,
    config: MainGateConfig<MAIN_GATE_T>,
    input: &input::assigned::PairedTrace<CMain::ScalarExt>,
) -> Result<input::assigned::SangriaAccumulatorInstance<CMain::ScalarExt>, Halo2PlonkError>
where
    CMain::ScalarExt: FromUniformBytes<64> + PrimeFieldBits,
{
    let bn_chip = bn_chip(config.clone());
    let ecc_chip = ecc_chip::<CSup>(config.clone());
    let mg = MainGate::new(config.clone());

    let r = ro_chip(config.clone())
        .absorb_iter(input.iter_wrap_values())
        .squeeze(region)
        .inspect_err(|err| error!("Error while computing 'r' in fold: {err:?}"))?;

    let r_bits = mg
        .le_num_to_bits(region, r.clone(), MAX_BITS)
        .inspect_err(|err| error!("Error while converting 'r' to bits in fold: {err:?}"))?;

    let r_as_bn = bn_chip
        .from_assigned_cell_to_limbs(region, &r)
        .inspect_err(|err| error!("Error while converting 'r' to BN limbs in fold: {err:?}"))
        .unwrap();

    let m_bn = module_as_bn::<CMain::ScalarExt, CMain::Base>()
        .inspect_err(|err| error!("Error while creating 'm_bn' in fold: {err:?}"))
        .unwrap();

    let mut acc = input.input_accumulator.clone();

    for input::assigned::PairedIncoming {
        instance:
            input::assigned::PairedPlonkInstance {
                W_commitments: input_W_commitments,
                challenges: input_challenges,
                instances: input_instances,
            },
        proof,
    } in input.incoming.iter()
    {
        let input::assigned::SangriaAccumulatorInstance {
            ins:
                input::assigned::PairedPlonkInstance {
                    W_commitments: acc_W_commitments,
                    instances: acc_instances,
                    challenges: acc_challenges,
                },
            E_commitment: acc_E_commitment,
            u: acc_u,
        } = &mut acc;

        *acc_W_commitments = FoldRelaxedPlonkInstanceChip::<
            MAIN_GATE_T,
            CSup,
            { sangria::CONSISTENCY_MARKERS_COUNT },
        >::fold_W(
            region,
            &config,
            &acc_W_commitments
                .iter()
                .cloned()
                .map(|(x, y)| AssignedPoint { x, y })
                .collect::<Box<[_]>>(),
            &input_W_commitments
                .iter()
                .cloned()
                .map(|(x, y)| AssignedPoint { x, y })
                .collect::<Box<[_]>>(),
            &r_bits,
        )
        .inspect_err(|err| error!("Error while folding W commitments in fold: {err:?}"))?
        .into_iter()
        .map(|p| (p.x, p.y))
        .collect();

        acc_instances
            .iter_mut()
            .zip_eq(input_instances)
            .try_for_each(
                |(acc_instance, input_instance)| -> Result<(), Halo2PlonkError> {
                    acc_instance
                        .iter_mut()
                        .zip_eq(input_instance)
                        .try_for_each(|(acc_cell, input_cell)| -> Result<(), Halo2PlonkError> {
                            *acc_cell = fold_relaxed_plonk_instance_chip::fold_via_biguint(
                                region,
                                &bn_chip,
                                input_cell,
                                acc_cell.to_vec(),
                                &m_bn,
                                &r_as_bn,
                                DEFAULT_LIMB_WIDTH,
                            )
                            .inspect_err(|err| {
                                error!("Error while folding instance cells in fold: {err:?}")
                            })?;

                            Ok(())
                        })?;

                    Ok(())
                },
            )
            .inspect_err(|err| error!("Error while folding instances in fold: {err:?}"))?;

        acc_challenges
            .iter_mut()
            .zip_eq(input_challenges.iter())
            .try_for_each(|(acc_cha, inp_cha)| -> Result<(), Halo2PlonkError> {
                *acc_cha = fold_relaxed_plonk_instance_chip::fold_via_biguint(
                    region,
                    &bn_chip,
                    inp_cha,
                    acc_cha.to_vec(),
                    &m_bn,
                    &r_as_bn,
                    DEFAULT_LIMB_WIDTH,
                )
                .inspect_err(|err| error!("Error while folding challenges in fold: {err:?}"))?;

                Ok(())
            })
            .inspect_err(|err| error!("Error while folding challenges in fold: {err:?}"))?;

        *acc_E_commitment = fold_relaxed_plonk_instance_chip::fold_E(
            region,
            &bn_chip,
            &ecc_chip,
            AssignedPoint {
                x: acc_E_commitment.0.clone(),
                y: acc_E_commitment.1.clone(),
            },
            &proof
                .iter()
                .cloned()
                .map(|(x, y)| AssignedPoint { x, y })
                .collect::<Box<[_]>>(),
            BigUintView {
                as_bn_limbs: r_as_bn.clone(),
                as_bits: r_bits.clone(),
            },
            &m_bn,
        )
        .inspect_err(|err| error!("Error while folding E commitment in fold: {err:?}"))?
        .into();

        *acc_u = mg
            .add(region, acc_u, &r)
            .inspect_err(|err| error!("Error while updating accumulator 'u' in fold: {err:?}"))?;
    }

    Ok(acc)
}
