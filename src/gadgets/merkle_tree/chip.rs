use itertools::Itertools;

use super::{
    off_circuit::{self as merkle_tree, NodeUpdate, Sibling},
    HasherChip, MainGateConfig, Spec,
};
use crate::{
    halo2_proofs::{
        circuit::AssignedCell,
        halo2curves::ff::{FromUniformBytes, PrimeFieldBits},
        plonk::ErrorFront as Halo2Error,
    },
    main_gate::{AdviceCyclicAssignor, RegionCtx, WrapValue},
};

pub struct MerkleTreeUpdateChip<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    spec: Spec<F>,
    proof: merkle_tree::Proof<F>,
}

impl<F> MerkleTreeUpdateChip<F>
where
    F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
{
    pub fn new(proof: merkle_tree::Proof<F>) -> Self {
        assert!(proof.verify());
        Self {
            spec: Spec::new(10, 10),
            proof,
        }
    }

    pub fn hasher_chip(&self, config: &MainGateConfig) -> HasherChip<F> {
        HasherChip::new(config.clone(), self.spec.clone())
    }

    /// Return assigned version of `NodeUpdate` with `root` information
    pub fn prove_next_update(
        &self,
        region: &mut RegionCtx<F>,
        config: MainGateConfig,
    ) -> Result<NodeUpdate<AssignedCell<F, F>>, Halo2Error> {
        let mut assigner = config.advice_cycle_assigner::<F>();
        let mut assigned_proof = self
            .proof
            .clone()
            .into_iter_with_level()
            .map(|(level, update)| {
                Result::<_, Halo2Error>::Ok((
                    merkle_tree::Index {
                        index: update.index,
                        level,
                    },
                    update.try_map(|f| assigner.assign_next_advice(region, || "TODO", f))?,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;
        region.next();

        for ((index, update), (_next_index, next_update)) in assigned_proof.iter().tuple_windows() {
            let (old_next, new_next) = match index
                .get_sibling()
                .map(|_| update.sibling.as_ref().expect("root unreachable"))
            {
                Sibling::Left(left) => {
                    let old_next = self
                        .hasher_chip(&config)
                        .update(&[left, &update.old].map(|c| WrapValue::Assigned(c.clone())))
                        .squeeze(region)?;
                    let new_next = self
                        .hasher_chip(&config)
                        .update(&[left, &update.new].map(|c| WrapValue::Assigned(c.clone())))
                        .squeeze(region)?;

                    (old_next, new_next)
                }
                Sibling::Right(right) => {
                    let old_next = self
                        .hasher_chip(&config)
                        .update(&[&update.old, right].map(|c| WrapValue::Assigned(c.clone())))
                        .squeeze(region)?;
                    let new_next = self
                        .hasher_chip(&config)
                        .update(&[&update.new, right].map(|c| WrapValue::Assigned(c.clone())))
                        .squeeze(region)?;

                    (old_next, new_next)
                }
            };

            assert_eq!(old_next.value().unwrap(), next_update.old.value().unwrap());
            assert_eq!(new_next.value().unwrap(), next_update.new.value().unwrap());

            region.constrain_equal(old_next.cell(), next_update.old.cell())?;
            region.constrain_equal(new_next.cell(), next_update.new.cell())?;
        }

        Ok(assigned_proof.pop().unwrap().1)
    }
}
