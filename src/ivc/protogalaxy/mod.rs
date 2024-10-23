mod verify_chip {
    use halo2_proofs::{
        halo2curves::{
            ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
            CurveAffine,
        },
        plonk::Error as Halo2PlonkError,
    };

    use crate::{
        gadgets::ecc::AssignedPoint,
        main_gate::{AdviceCyclicAssignor, AssignedValue, MainGateConfig, RegionCtx},
        nifs::protogalaxy,
        plonk::PlonkInstance,
        poseidon::ROCircuitTrait,
        util::ScalarToBase,
    };

    #[derive(Debug, thiserror::Error)]
    pub enum Error {
        #[error("Error while assign {annotation}: {err:?}")]
        Assign {
            annotation: &'static str,
            err: Halo2PlonkError,
        },
    }

    /// Assigned version of [`crate::plonk::PlonkInstance`]
    pub struct AssignedPlonkInstance<C: CurveAffine> {
        W_commitments: Vec<AssignedPoint<C>>,
        instances: Vec<Vec<AssignedValue<C::Base>>>,
        challenges: Vec<AssignedValue<C::Base>>,
    }

    impl<C: CurveAffine> AssignedPlonkInstance<C> {
        pub fn assign<const T: usize>(
            region: &mut RegionCtx<C::Base>,
            main_gate_config: MainGateConfig<T>,
            pi: PlonkInstance<C>,
        ) -> Result<Self, Error> {
            let PlonkInstance {
                W_commitments,
                instances,
                challenges,
            } = pi;

            let mut assigner = main_gate_config.advice_cycle_assigner();

            let W_commitments = W_commitments
                .iter()
                .enumerate()
                .map(|(i, W_commitment)| {
                    assigner.assign_next_advice_point(
                        region,
                        || format!("W_commitments[{i}]"),
                        W_commitment,
                    )
                })
                .collect::<Result<Vec<_>, _>>();

            let instances = instances
                .iter()
                .map(|instance| {
                    assigner.assign_all_advice(
                        region,
                        || "instance",
                        instance.iter().map(|i| C::scalar_to_base(i).unwrap()),
                    )
                })
                .collect::<Result<Vec<_>, _>>();

            let challenges = assigner.assign_all_advice(
                region,
                || "challenges",
                challenges.iter().map(|i| C::scalar_to_base(i).unwrap()),
            );

            let map_err = |err| Error::Assign {
                annotation: "PlonkInstance",
                err,
            };

            Ok(Self {
                W_commitments: W_commitments.map_err(map_err)?,
                instances: instances.map_err(map_err)?,
                challenges: challenges.map_err(map_err)?,
            })
        }
    }

    /// Assigned version of [`crate::nifs::protogalaxy::accumulator::AccumulatorInstance`]
    pub struct AssignedAccumulatorInstance<C: CurveAffine> {
        ins: AssignedPlonkInstance<C>,
        betas: Box<[AssignedValue<C::Base>]>,
        e: AssignedValue<C::Base>,
    }

    impl<C: CurveAffine> AssignedAccumulatorInstance<C> {
        pub fn assign<const T: usize>(
            region: &mut RegionCtx<C::Base>,
            main_gate_config: MainGateConfig<T>,
            acc: protogalaxy::AccumulatorInstance<C>,
        ) -> Result<Self, Error> {
            let protogalaxy::AccumulatorInstance { ins, betas, e } = acc;

            let ins = AssignedPlonkInstance::assign(region, main_gate_config.clone(), ins)?;

            let mut assigner = main_gate_config.advice_cycle_assigner();

            // Convert and assign `betas`
            let betas = betas
                .iter()
                .map(|beta| {
                    assigner.assign_next_advice(
                        region,
                        || "beta",
                        C::scalar_to_base(beta).unwrap(), // assuming conversion to base field is needed
                    )
                })
                .collect::<Result<Vec<_>, _>>()
                .map_err(|err| Error::Assign {
                    annotation: "AccumulatorInstance::betas",
                    err,
                })?
                .into_boxed_slice();

            // Convert and assign `e`
            let e = assigner
                .assign_next_advice(region, || "e", C::scalar_to_base(&e).unwrap())
                .map_err(|err| Error::Assign {
                    annotation: "AccumulatorInstance::e",
                    err,
                })?;

            Ok(Self { ins, betas, e })
        }
    }

    pub struct AssignedProof<F: PrimeField> {
        poly_F: Box<[AssignedValue<F>]>,
        poly_K: Box<[AssignedValue<F>]>,
    }

    impl<F: PrimeField> AssignedProof<F> {
        pub fn assign<const T: usize>(
            region: &mut RegionCtx<F>,
            main_gate_config: MainGateConfig<T>,
            proof: protogalaxy::Proof<F>,
        ) -> Result<Self, Error> {
            let protogalaxy::Proof { poly_K, poly_F } = proof;

            let mut assigner = main_gate_config.advice_cycle_assigner();

            Ok(Self {
                poly_F: assigner
                    .assign_all_advice(region, || "poly_F", poly_F.iter().copied())
                    .map_err(|err| Error::Assign {
                        annotation: "proof::poly_F",
                        err,
                    })?
                    .into_boxed_slice(),
                poly_K: assigner
                    .assign_all_advice(region, || "poly_K", poly_K.iter().copied())
                    .map_err(|err| Error::Assign {
                        annotation: "proof::poly_k",
                        err,
                    })?
                    .into_boxed_slice(),
            })
        }
    }

    pub struct AssignedVerifierParam<C: CurveAffine> {
        pp_digest: AssignedPoint<C>,
    }

    impl<C: CurveAffine> AssignedVerifierParam<C> {
        pub fn assign<const T: usize>(
            region: &mut RegionCtx<C::Base>,
            main_gate_config: MainGateConfig<T>,
            vp: protogalaxy::VerifierParam<C>,
        ) -> Result<Self, Error> {
            let protogalaxy::VerifierParam { pp_digest } = vp;

            Ok(Self {
                pp_digest: main_gate_config
                    .advice_cycle_assigner::<C::Base>()
                    .assign_next_advice_point(region, || "pp_digest", &pp_digest)
                    .map_err(|err| Error::Assign {
                        annotation: "VerifierParam",
                        err,
                    })?,
            })
        }
    }

    /// Assigned version of `fn verify` logic from [`crate::nifs::protogalaxy::ProtoGalaxy`].
    pub fn verify<C: CurveAffine, const L: usize>(
        _region: &mut RegionCtx<C::Base>,
        _ro_circuit: impl ROCircuitTrait<C::ScalarExt>,
        _vp: protogalaxy::VerifierParam<C>,
        _accumulator: AssignedAccumulatorInstance<C>,
        _incoming: &[AssignedPlonkInstance<C>],
        _proof: AssignedProof<C::ScalarExt>,
    ) -> Result<AssignedAccumulatorInstance<C>, Error>
    where
        C::ScalarExt: FromUniformBytes<64> + PrimeFieldBits,
    {
        todo!()
    }
}
