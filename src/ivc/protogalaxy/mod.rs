mod verify_chip {
    use std::iter;

    use halo2_proofs::{
        halo2curves::{
            ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
            CurveAffine,
        },
        plonk::Error as Halo2PlonkError,
    };

    use crate::{
        gadgets::ecc::AssignedPoint,
        main_gate::{AdviceCyclicAssignor, AssignedValue, MainGateConfig, RegionCtx, WrapValue},
        nifs::protogalaxy,
        plonk::PlonkInstance,
        polynomial::univariate::UnivariatePoly,
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

        #[error("Error while squeeze challenges: {err:?}")]
        Squeeze { err: Halo2PlonkError },
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

        pub fn iter_wrap_value(&self) -> impl '_ + Iterator<Item = WrapValue<C::Base>> {
            let Self {
                W_commitments,
                instances,
                challenges,
            } = self;

            W_commitments
                .iter()
                .flat_map(|W_commitment| WrapValue::from_assigned_point(W_commitment).into_iter())
                .chain(instances.iter().flat_map(|instance| {
                    instance
                        .iter()
                        .map(|value| WrapValue::Assigned(value.clone()))
                }))
                .chain(
                    challenges
                        .iter()
                        .map(|challenge| WrapValue::Assigned(challenge.clone())),
                )
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

        pub fn iter_wrap_value(&self) -> impl '_ + Iterator<Item = WrapValue<C::Base>> {
            let Self { ins, betas, e } = self;

            ins.iter_wrap_value()
                .chain(betas.iter().map(|beta| WrapValue::Assigned(beta.clone())))
                .chain(iter::once(WrapValue::Assigned(e.clone())))
        }
    }

    /// Assigned version of [`crate::polynomial::univariate::UnivariatePoly`]
    pub struct AssignedUnivariatePoly<F: PrimeField>(Box<[AssignedValue<F>]>);

    impl<F: PrimeField> AssignedUnivariatePoly<F> {
        pub fn assign<const T: usize>(
            region: &mut RegionCtx<F>,
            main_gate_config: MainGateConfig<T>,
            annotation: &'static str,
            poly: &UnivariatePoly<F>,
        ) -> Result<Self, Error> {
            let up = AssignedUnivariatePoly(
                main_gate_config
                    .advice_cycle_assigner()
                    .assign_all_advice(region, || annotation, poly.iter().copied())
                    .map_err(|err| Error::Assign { annotation, err })?
                    .into_boxed_slice(),
            );

            region.next();

            Ok(up)
        }

        pub fn iter_wrap_value(&self) -> impl '_ + Iterator<Item = WrapValue<F>> {
            self.0
                .iter()
                .map(|coeff| WrapValue::Assigned(coeff.clone()))
        }
    }

    /// Assigned version of [`crate::nifs::protogalaxy::Proof]
    pub struct AssignedProof<F: PrimeField> {
        poly_F: AssignedUnivariatePoly<F>,
        poly_K: AssignedUnivariatePoly<F>,
    }

    impl<F: PrimeField> AssignedProof<F> {
        pub fn assign<const T: usize>(
            region: &mut RegionCtx<F>,
            main_gate_config: MainGateConfig<T>,
            proof: protogalaxy::Proof<F>,
        ) -> Result<Self, Error> {
            let protogalaxy::Proof { poly_K, poly_F } = proof;

            Ok(Self {
                poly_F: AssignedUnivariatePoly::assign::<T>(
                    region,
                    main_gate_config.clone(),
                    "poly_F",
                    &poly_F,
                )?,
                poly_K: AssignedUnivariatePoly::assign::<T>(
                    region,
                    main_gate_config.clone(),
                    "poly_K",
                    &poly_K,
                )?,
            })
        }
    }

    /// Assigned version of [`crate::nifs::protogalaxy::VerifierParam`]
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

    /// Assigned version of [`crate::nifs::protogalaxy::Challenges`]
    struct AssignedChallanges<C: CurveAffine> {
        delta: AssignedValue<C::Base>,
        alpha: AssignedValue<C::Base>,
        gamma: AssignedValue<C::Base>,
    }

    impl<C: CurveAffine> AssignedChallanges<C> {
        fn generate(
            region: &mut RegionCtx<C::Base>,
            mut ro_circuit: impl ROCircuitTrait<C::Base>,
            vp: AssignedVerifierParam<C>,
            accumulator: AssignedAccumulatorInstance<C>,
            incoming: &[AssignedPlonkInstance<C>],
            proof: AssignedProof<C::Base>,
        ) -> Result<AssignedChallanges<C>, Halo2PlonkError>
        where
            C::Base: FromUniformBytes<64> + PrimeFieldBits,
            C::ScalarExt: FromUniformBytes<64> + PrimeFieldBits,
        {
            let delta = ro_circuit
                .absorb_point(WrapValue::from_assigned_point(&vp.pp_digest))
                .absorb_iter(accumulator.iter_wrap_value())
                .absorb_iter(incoming.iter().flat_map(|tr| tr.iter_wrap_value()))
                .squeeze(region)?;

            let alpha = ro_circuit
                .absorb_iter(proof.poly_F.iter_wrap_value())
                .squeeze(region)?;

            let gamma = ro_circuit
                .absorb_iter(proof.poly_K.iter_wrap_value())
                .squeeze(region)?;

            Ok(AssignedChallanges {
                delta,
                alpha,
                gamma,
            })
        }
    }

    /// Assigned version of `fn verify` logic from [`crate::nifs::protogalaxy::ProtoGalaxy`].
    ///
    /// # Algorithm
    ///
    /// The logic of the proof generation follows several key steps:
    ///
    /// 1. **Generate Delta:**
    ///     - **RO Seeds**: includes all input parameters except `ck`
    ///     - `delta = ro_acc.squeeze()`
    ///
    /// 2. **Generate Alpha:**
    ///     - **RO Update**: absorb `proof.poly_F`
    ///     - `alpha = ro_acc.squeeze()`
    ///
    /// 3. **Update Beta* Values:**
    ///     - `beta*[i] = beta[i] + alpha * delta[i]`
    ///
    /// 4. **Generate Gamma:**
    ///     - **RO Update**: Absorb `proof.poly_K`
    ///     - `gamma = ro_acc.squeeze()`
    ///
    /// 5. **Fold the Instance:**
    ///     - [`ProtoGalaxy::fold_instance`]
    pub fn verify<C: CurveAffine, const L: usize>(
        region: &mut RegionCtx<C::Base>,
        ro_circuit: impl ROCircuitTrait<C::Base>,
        vp: AssignedVerifierParam<C>,
        accumulator: AssignedAccumulatorInstance<C>,
        incoming: &[AssignedPlonkInstance<C>],
        proof: AssignedProof<C::Base>,
    ) -> Result<AssignedAccumulatorInstance<C>, Error>
    where
        C::Base: FromUniformBytes<64> + PrimeFieldBits,
        C::ScalarExt: FromUniformBytes<64> + PrimeFieldBits,
    {
        let AssignedChallanges {
            delta: _,
            alpha: _,
            gamma: _,
        } = AssignedChallanges::generate(region, ro_circuit, vp, accumulator, incoming, proof)
            .map_err(|err| Error::Squeeze { err })?;

        todo!()
    }

    #[cfg(test)]
    mod tests {
        use halo2_proofs::halo2curves::{bn256::G1Affine, group::prime::PrimeCurveAffine};

        use super::*;
        use crate::{
            nifs::{
                self,
                protogalaxy::{AccumulatorArgs, VerifierParam},
            },
            poseidon::{PoseidonHash, ROTrait, Spec},
        };

        type C = G1Affine;

        struct Mock {
            params: VerifierParam<C>,
            spec: Spec<<C as CurveAffine>::Base, 5, 4>,
            acc: nifs::protogalaxy::Accumulator<C>,
            proof: nifs::protogalaxy::Proof<<C as CurveAffine>::ScalarExt>,
        }

        impl Mock {
            fn new() -> Self {
                let params = VerifierParam::<C> {
                    pp_digest: C::identity(),
                };

                let spec = Spec::<<C as CurveAffine>::Base, 5, 4>::new(10, 10);

                let acc = nifs::protogalaxy::Accumulator::<C>::new(
                    AccumulatorArgs {
                        num_io: Box::new([]),
                        num_challenges: 0,
                        num_witness: 0,
                        k_table_size: 0,
                        round_sizes: Box::new([]),
                    },
                    10,
                );

                let proof = nifs::protogalaxy::Proof {
                    poly_F: UnivariatePoly::<<C as CurveAffine>::ScalarExt>::new_zeroed(10),
                    poly_K: UnivariatePoly::new_zeroed(10),
                };

                Self {
                    params,
                    spec,
                    acc,
                    proof,
                }
            }
        }

        #[test]
        fn challanges() {
            let m = Mock::new();

            let _challenges = nifs::protogalaxy::Challenges::generate(
                &m.params,
                &mut PoseidonHash::new(m.spec),
                &m.acc,
                iter::empty::<&PlonkInstance<C>>(),
                &m.proof,
            );
        }
    }
}
