use std::{iter, num::NonZeroUsize};

use halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits};
use tracing::{debug, instrument};

use crate::{
    main_gate::{AssignedValue, MainGateConfig, RegionCtx},
    poseidon::{
        poseidon_circuit::PoseidonChip, random_oracle::ROCircuitTrait, PoseidonHash, ROTrait, Spec,
    },
    util,
};

#[instrument(skip_all)]
pub fn fold_step_circuit_instances_hash_accumulator<F1, F2>(
    instances_hash_accumulator: &F1,
    instances: &[Vec<F1>],
) -> F1
where
    F1: PrimeFieldBits + FromUniformBytes<64>,
    F2: PrimeFieldBits + FromUniformBytes<64>,
{
    debug!(
        "MODS {:?}|{:?}",
        std::any::TypeId::of::<F1>(),
        std::any::TypeId::of::<F2>()
    );

    let hash_in_f1: F2 = PoseidonHash::<F2>::default()
        .absorb_field_iter(
            iter::once(instances_hash_accumulator)
                .chain(instances.iter().flat_map(|instance| instance.iter()))
                .map(|i| util::fe_to_fe(i).unwrap()),
        )
        .inspect(|buf| debug!("off-circuit buf of instances: {buf:?}"))
        .output::<F2>(NonZeroUsize::new(<F1 as PrimeField>::NUM_BITS as usize).unwrap());

    debug!("output is {hash_in_f1:?}");

    util::fe_to_fe(&hash_in_f1).unwrap()
}

#[instrument(skip_all)]
pub fn fold_assign_step_circuit_instances_hash_accumulator<F>(
    ctx: &mut RegionCtx<'_, F>,
    config: MainGateConfig<5>,
    input_instances: &[AssignedValue<F>],
    folded_instances: &AssignedValue<F>,
) -> Result<AssignedValue<F>, halo2_proofs::plonk::Error>
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    debug!("MODS {:?}", std::any::TypeId::of::<F>());

    let hash_in_base = PoseidonChip::<F, 5, 4>::new(config, Spec::default())
        .absorb_base(folded_instances.into())
        .absorb_iter(input_instances.iter())
        .inspect(|buf| debug!("on-circuit buf of instances: {buf:?}"))
        .squeeze(ctx)?;

    debug!("output is {hash_in_base:?}");

    Ok(hash_in_base)
}
