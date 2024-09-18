use halo2_proofs::halo2curves::{
    ff::{FromUniformBytes, PrimeFieldBits},
    CurveAffine,
};

use crate::{
    constants::NUM_CHALLENGE_BITS,
    main_gate::{AssignedValue, MainGateConfig, RegionCtx},
    poseidon::{
        poseidon_circuit::PoseidonChip, random_oracle::ROCircuitTrait, PoseidonHash, ROTrait, Spec,
    },
    util,
};

pub fn fold_step_circuit_instances_hash_accumulator<F>(
    instances_hash_accumulator: &F,
    instances: &[Vec<F>],
) -> F
where
    F: PrimeFieldBits + FromUniformBytes<64>,
{
    PoseidonHash::<F>::default()
        .absorb_field(util::fe_to_fe(instances_hash_accumulator).unwrap())
        .absorb_field_iter(
            instances
                .iter()
                .flat_map(|instance| instance.iter())
                .map(|i| util::fe_to_fe(i).unwrap()),
        )
        .output(NUM_CHALLENGE_BITS)
}

pub fn fold_assign_step_circuit_instances_hash_accumulator<C: CurveAffine>(
    ctx: &mut RegionCtx<'_, C::Base>,
    config: MainGateConfig<5>,
    input_instances: &[AssignedValue<C::Base>],
    folded_instances: &AssignedValue<C::Base>,
) -> Result<AssignedValue<C::Base>, halo2_proofs::plonk::Error>
where
    C::Base: PrimeFieldBits + FromUniformBytes<64>,
{
    PoseidonChip::<C::Base, 5, 4>::new(config, Spec::default())
        .absorb_base(folded_instances.into())
        .absorb_iter(input_instances.iter())
        .squeeze(ctx)
}
