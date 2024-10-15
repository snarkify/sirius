mod verify_chip {
    use halo2_proofs::halo2curves::{
        ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
        CurveAffine,
    };

    use crate::{
        gadgets::ecc::AssignedPoint,
        main_gate::{AssignedValue, RegionCtx},
        nifs::protogalaxy,
        plonk::PlonkInstance,
        poseidon::ROCircuitTrait,
    };

    #[derive(Debug, thiserror::Error)]
    pub enum Error {}

    /// Assigned version of [`crate::plonk::PlonkInstance`]
    pub struct AssignedPlonkInstance<C: CurveAffine> {
        W_commitments: Vec<AssignedPoint<C>>,
        instances: Vec<Vec<AssignedValue<C::ScalarExt>>>,
        challenges: Vec<AssignedValue<C::ScalarExt>>,
    }

    impl<C: CurveAffine> AssignedPlonkInstance<C> {
        pub fn assign(_pi: PlonkInstance<C>) -> Result<Self, Error> {
            todo!()
        }
    }

    /// Assigned version of [`crate::nifs::protogalaxy::accumulator::AccumulatorInstance`]
    pub struct AssignedAccumulatorInstance<C: CurveAffine> {
        ins: AssignedPlonkInstance<C>,
        betas: Box<[AssignedValue<C::ScalarExt>]>,
        e: AssignedValue<C::ScalarExt>,
    }

    impl<C: CurveAffine> AssignedAccumulatorInstance<C> {
        pub fn assign(_acc: protogalaxy::AccumulatorInstance<C>) -> Result<Self, Error> {
            todo!()
        }
    }

    pub struct AssignedProof<F: PrimeField> {
        poly_F: Box<[AssignedValue<F>]>,
        poly_K: Box<[AssignedValue<F>]>,
    }

    impl<F: PrimeField> AssignedProof<F> {
        pub fn assign(_proof: protogalaxy::Proof<F>) -> Result<Self, Error> {
            todo!()
        }
    }

    /// Assigned version of `fn verify` logic from [`crate::nifs::protogalaxy::ProtoGalaxy`].
    pub fn verify<C: CurveAffine>(
        _region: &mut RegionCtx<C::Base>,
        _ro_circuit: impl ROCircuitTrait<C::ScalarExt>,
        _accumulator: AssignedAccumulatorInstance<C>,
        _incoming: &[PlonkInstance<C>],
        _proof: AssignedProof<C::ScalarExt>,
    ) -> Result<AssignedAccumulatorInstance<C>, Error>
    where
        C::ScalarExt: FromUniformBytes<64> + PrimeFieldBits,
    {
        todo!()
    }
}
