use std::{array, ops::Deref};

use super::super::{DEFAULT_LIMBS_COUNT, DEFAULT_LIMB_WIDTH};
pub use crate::ivc::protogalaxy::verify_chip::BigUintPoint;
use crate::{
    gadgets::nonnative::bn::big_uint::BigUint,
    halo2_proofs::halo2curves::{ff::PrimeField, CurveAffine},
    ivc::cyclefold::support_circuit,
    nifs, plonk,
    polynomial::univariate::UnivariatePoly,
    poseidon::{AbsorbInRO, ROTrait},
    util,
};

pub mod assigned;

#[derive(Debug, Clone)]
pub struct NativePlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<BigUintPoint<F>>,
    pub(crate) instances: Vec<Vec<F>>,
    pub(crate) challenges: Vec<F>,
}

impl<F: PrimeField> NativePlonkInstance<F> {
    pub fn new<CMain: CurveAffine<ScalarExt = F>>(acc: &plonk::PlonkInstance<CMain>) -> Self {
        let plonk::PlonkInstance {
            W_commitments,
            instances,
            challenges,
        } = acc;

        Self {
            W_commitments: W_commitments
                .iter()
                .map(|commitment| BigUintPoint::new(commitment).unwrap())
                .collect(),
            instances: instances.to_vec(),
            challenges: challenges.to_vec(),
        }
    }
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for NativePlonkInstance<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            W_commitments,
            instances,
            challenges,
        } = self;
        ro.absorb_iter(W_commitments.iter())
            .absorb_field_iter(instances.iter().flatten().cloned())
            .absorb_field_iter(challenges.iter().cloned());
    }
}

#[derive(Debug, Clone)]
pub struct PairedPlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<(F, F)>,
    pub(crate) instances: Vec<Vec<BigUint<F>>>,
    pub(crate) challenges: Vec<BigUint<F>>,
}

impl<F: PrimeField> PairedPlonkInstance<F> {
    pub fn new<CSup: CurveAffine<Base = F>>(
        acc: &nifs::sangria::FoldablePlonkInstance<CSup, { support_circuit::INSTANCES_LEN }>,
    ) -> Self {
        let nifs::sangria::PlonkInstance {
            W_commitments,
            instances,
            challenges,
        } = acc.deref();
        Self {
            W_commitments: W_commitments
                .iter()
                .map(|commit| {
                    let c = commit.coordinates().unwrap();
                    (*c.x(), *c.y())
                })
                .collect(),
            instances: instances
                .iter()
                .map(|instance| {
                    instance
                        .iter()
                        .map(|value| {
                            BigUint::from_different_field(
                                value,
                                DEFAULT_LIMB_WIDTH,
                                DEFAULT_LIMBS_COUNT,
                            )
                            .unwrap()
                        })
                        .collect()
                })
                .collect(),
            challenges: challenges
                .iter()
                .map(|cha| {
                    BigUint::from_different_field(cha, DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT)
                        .unwrap()
                })
                .collect(),
        }
    }
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for PairedPlonkInstance<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            W_commitments,
            instances,
            challenges,
        } = self;

        ro.absorb_field_iter(W_commitments.iter().flat_map(|(x, y)| [x, y]).copied())
            .absorb_iter(instances.iter().flatten())
            .absorb_iter(challenges.iter());
    }
}

impl<C: CurveAffine> From<plonk::PlonkInstance<C>> for NativePlonkInstance<C::ScalarExt> {
    fn from(value: plonk::PlonkInstance<C>) -> Self {
        Self {
            W_commitments: value
                .W_commitments
                .iter()
                .map(BigUintPoint::new)
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
            instances: value.instances,
            challenges: value.challenges,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProtoGalaxyAccumulatorInstance<F: PrimeField> {
    pub(crate) ins: NativePlonkInstance<F>,
    pub(crate) betas: Box<[F]>,
    pub(crate) e: F,
}

impl<F: PrimeField> ProtoGalaxyAccumulatorInstance<F> {
    pub fn new<CMain: CurveAffine<ScalarExt = F>>(
        acc: &nifs::protogalaxy::AccumulatorInstance<CMain>,
    ) -> Self {
        let nifs::protogalaxy::AccumulatorInstance { ins, betas, e } = acc;

        let ins = NativePlonkInstance::new(ins);

        Self {
            ins,
            betas: betas.clone(),
            e: *e,
        }
    }
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for ProtoGalaxyAccumulatorInstance<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self { ins, betas, e } = self;

        ro.absorb(ins)
            .absorb_field_iter(betas.iter().cloned())
            .absorb_field(*e);
    }
}

/// Recursive trace of the circuit itself
#[derive(Debug, Clone)]
pub struct SelfTrace<F: PrimeField> {
    pub input_accumulator: ProtoGalaxyAccumulatorInstance<F>,
    pub incoming: NativePlonkInstance<F>,
    pub proof: nifs::protogalaxy::Proof<F>,
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for SelfTrace<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            input_accumulator,
            incoming,
            proof,
        } = self;

        let nifs::protogalaxy::Proof { poly_F, poly_K } = proof;

        ro.absorb(input_accumulator)
            .absorb(incoming)
            .absorb_field_iter(poly_K.iter().chain(poly_F.iter()).copied());
    }
}

impl<F: PrimeField> SelfTrace<F> {
    pub fn new_initial(native_plonk_structure: &plonk::PlonkStructure<F>) -> Self {
        // SPS protocol setup
        let (W_commitments_len, challenges_len) = match native_plonk_structure.num_challenges {
            0 => (1, 0),
            1 => (1, 1),
            2 => (2, 2),
            3 => (3, 3),
            _ => unreachable!(">3 challenges can't be"),
        };

        let ins = NativePlonkInstance::<F> {
            W_commitments: vec![BigUintPoint::<F>::identity(); W_commitments_len],
            instances: native_plonk_structure
                .num_io
                .iter()
                .map(|len| vec![F::ZERO; *len])
                .collect(),
            challenges: vec![F::ZERO; challenges_len],
        };
        let count_of_eval =
            nifs::protogalaxy::poly::get_count_of_valuation_with_padding(native_plonk_structure)
                .unwrap()
                .get();
        let proof_len = count_of_eval.ilog2() as usize;

        SelfTrace {
            input_accumulator: ProtoGalaxyAccumulatorInstance {
                ins: ins.clone(),
                betas: vec![F::ZERO; proof_len].into_boxed_slice(),
                e: F::ZERO,
            },
            incoming: ins,
            proof: nifs::protogalaxy::Proof {
                poly_F: UnivariatePoly::new_zeroed(proof_len),
                poly_K: UnivariatePoly::new_zeroed(proof_len),
            },
        }
    }

    fn W_commitments_len(&self) -> usize {
        self.input_accumulator.ins.W_commitments.len()
    }
}

#[derive(Debug, Clone)]
pub struct SangriaAccumulatorInstance<F: PrimeField> {
    pub(crate) ins: PairedPlonkInstance<F>,
    pub(crate) E_commitment: (F, F),
    pub(crate) u: F,
}

impl<F: PrimeField> SangriaAccumulatorInstance<F> {
    pub fn new<CSup: CurveAffine<Base = F>>(
        acc: &nifs::sangria::RelaxedPlonkInstance<CSup, { support_circuit::INSTANCES_LEN }>,
    ) -> Self {
        let nifs::sangria::RelaxedPlonkInstance {
            W_commitments,
            consistency_markers,
            challenges,
            E_commitment,
            u,
            step_circuit_instances_hash_accumulator: _,
        } = acc;

        Self {
            ins: PairedPlonkInstance {
                W_commitments: W_commitments
                    .iter()
                    .map(|commitment| {
                        let c = commitment.coordinates().unwrap();
                        (*c.x(), *c.y())
                    })
                    .collect(),
                // TODO #369 Make markers
                instances: vec![consistency_markers
                    .iter()
                    .map(|instance| {
                        BigUint::from_different_field(
                            instance,
                            DEFAULT_LIMB_WIDTH,
                            DEFAULT_LIMBS_COUNT,
                        )
                        .unwrap()
                    })
                    .collect()],
                challenges: challenges
                    .iter()
                    .map(|cha| {
                        BigUint::from_different_field(cha, DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT)
                            .unwrap()
                    })
                    .collect(),
            },
            E_commitment: {
                let c = E_commitment.coordinates().unwrap();
                (*c.x(), *c.y())
            },
            u: util::fe_to_fe(u).unwrap(),
        }
    }
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for SangriaAccumulatorInstance<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            ins,
            E_commitment: (ex, ey),
            u,
        } = self;

        ro.absorb(ins)
            .absorb_field(*ex)
            .absorb_field(*ey)
            .absorb_field(*u);
    }
}

#[derive(Debug, Clone)]
pub struct PairedIncoming<F: PrimeField> {
    instance: PairedPlonkInstance<F>,
    proof: nifs::sangria::CrossTermCommits<(F, F)>,
}

impl<F: PrimeField> PairedIncoming<F> {
    pub fn new<CSup: CurveAffine<Base = F>>(
        instance: &nifs::sangria::FoldablePlonkInstance<CSup, { support_circuit::INSTANCES_LEN }>,
        proof: &nifs::sangria::CrossTermCommits<CSup>,
    ) -> Self {
        let proof = proof
            .iter()
            .map(|commit| {
                let c = commit.coordinates().unwrap();
                (*c.x(), *c.y())
            })
            .collect::<Vec<_>>();
        let instance = PairedPlonkInstance::new(instance);

        Self { instance, proof }
    }
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for PairedIncoming<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self { instance, proof } = self;
        let proof_iter = proof.iter().flat_map(|(a, b)| [a, b]).copied();

        ro.absorb(instance).absorb_field_iter(proof_iter);
    }
}

#[derive(Debug, Clone)]
pub struct PairedTrace<F: PrimeField> {
    pub input_accumulator: SangriaAccumulatorInstance<F>,
    // The size from one to three
    // Depdend on `W_commitments_len`
    pub incoming: Box<[PairedIncoming<F>]>,
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for PairedTrace<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            input_accumulator,
            incoming,
        } = self;

        ro.absorb(input_accumulator).absorb_iter(incoming.iter());
    }
}

impl<F: PrimeField> PairedTrace<F> {
    pub fn new_initial<CSup: CurveAffine<Base = F>>(
        paired_plonk_structure: &plonk::PlonkStructure<CSup::ScalarExt>,
        paired_plonk_instance: &nifs::sangria::FoldablePlonkInstance<
            CSup,
            { support_circuit::INSTANCES_LEN },
        >,
        W_commitments_len: usize,
    ) -> Self {
        let ins = PairedPlonkInstance {
            W_commitments: paired_plonk_instance
                .W_commitments
                .iter()
                .map(|p| {
                    let c = p.coordinates().unwrap();
                    (*c.x(), *c.y())
                })
                .collect(),
            instances: paired_plonk_instance
                .instances
                .iter()
                .map(|col| {
                    col.iter()
                        .map(|value| {
                            BigUint::from_different_field(
                                value,
                                DEFAULT_LIMB_WIDTH,
                                DEFAULT_LIMBS_COUNT,
                            )
                            .unwrap()
                        })
                        .collect()
                })
                .collect(),
            challenges: paired_plonk_instance
                .challenges
                .iter()
                .map(|value| {
                    BigUint::from_different_field(value, DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT)
                        .unwrap()
                })
                .collect(),
        };

        let pairing = PairedIncoming {
            instance: ins.clone(),
            proof: vec![
                (F::ZERO, F::ZERO);
                paired_plonk_structure
                    .get_degree_for_folding()
                    .saturating_sub(1)
            ],
        };
        Self {
            input_accumulator: SangriaAccumulatorInstance {
                ins: ins.clone(),
                E_commitment: (F::ZERO, F::ZERO),
                u: F::ZERO,
            },
            incoming: vec![pairing; W_commitments_len].into_boxed_slice(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Input<const ARITY: usize, F: PrimeField> {
    pub pp_digest: (F, F),

    /// We should check-consistency with delegated part
    pub self_trace: SelfTrace<F>,

    /// One to three traces of support_circuit from paired curve
    /// We should fold challenge (r) as BigUint
    ///
    /// Circuit Field is `C::ScalarExt`
    ///
    /// [instances, challenges] fields will be BigUint
    pub paired_trace: PairedTrace<F>,

    pub step: usize,
    pub z_0: [F; ARITY],
    pub z_i: [F; ARITY],
}

#[cfg(test)]
impl<const ARITY: usize, F: PrimeField> Input<ARITY, F> {
    pub fn random<R: rand::Rng + ?Sized>(mut rng: &mut R) -> Self {
        use std::iter;

        // Initialize `step` with a random value.
        let step: usize = rng.gen();

        // Create an infinite generator of random field elements.
        let mut gen = iter::repeat_with(move || F::random(&mut rng));

        // Helper closure to create a random BigUint<F>
        fn random_big_uint<F: PrimeField>(gen: &mut impl Iterator<Item = F>) -> BigUint<F> {
            BigUint::from_f(
                &gen.next().unwrap(),
                DEFAULT_LIMB_WIDTH,
                DEFAULT_LIMBS_COUNT,
            )
            .expect("Failed to create BigUint from limbs")
        }

        // Initialize `pp_digest` with random field elements.
        let pp_digest = (gen.next().unwrap(), gen.next().unwrap());

        // Initialize `self_trace` with random values.
        let self_trace = SelfTrace {
            input_accumulator: ProtoGalaxyAccumulatorInstance {
                ins: NativePlonkInstance {
                    W_commitments: vec![BigUintPoint {
                        x: random_big_uint(&mut gen).limbs().try_into().unwrap(),
                        y: random_big_uint(&mut gen).limbs().try_into().unwrap(),
                    }],
                    instances: vec![
                        vec![gen.next().unwrap(); 10]; // 5 instances each with 10 field elements
                        1
                    ],
                    challenges: vec![gen.next().unwrap(); 1],
                },
                betas: vec![gen.next().unwrap()].into_boxed_slice(),
                e: gen.next().unwrap(),
            },
            incoming: NativePlonkInstance {
                W_commitments: vec![BigUintPoint {
                    x: random_big_uint(&mut gen).limbs().try_into().unwrap(),
                    y: random_big_uint(&mut gen).limbs().try_into().unwrap(),
                }],
                instances: vec![
                    vec![gen.next().unwrap(); 10]; // 10 instances each with 10 field elements
                    1
                ],
                challenges: vec![gen.next().unwrap(); 1],
            },
            proof: nifs::protogalaxy::Proof {
                poly_F: UnivariatePoly::from_iter(
                    iter::repeat_with(|| gen.next().unwrap()).take(1),
                ),
                poly_K: UnivariatePoly::from_iter(
                    iter::repeat_with(|| gen.next().unwrap()).take(2),
                ),
            },
        };

        // Initialize `paired_trace` with random values.
        let paired_trace = PairedTrace {
            input_accumulator: SangriaAccumulatorInstance {
                ins: PairedPlonkInstance {
                    W_commitments: vec![(gen.next().unwrap(), gen.next().unwrap()); 1],
                    instances: vec![vec![random_big_uint(&mut gen); 8]; 1],
                    challenges: vec![random_big_uint(&mut gen); 1],
                },
                E_commitment: (gen.next().unwrap(), gen.next().unwrap()),
                u: gen.next().unwrap(),
            },
            incoming: vec![
                PairedIncoming {
                    instance: PairedPlonkInstance {
                        W_commitments: vec![(gen.next().unwrap(), gen.next().unwrap()); 1],
                        instances: vec![vec![random_big_uint(&mut gen); 8]; 1],
                        challenges: vec![random_big_uint(&mut gen); 1],
                    },
                    proof: vec![(gen.next().unwrap(), gen.next().unwrap()); 1],
                };
                1
            ]
            .into_boxed_slice(),
        };

        // Initialize `z_0` and `z_i` arrays with random field elements.
        let z_0 = array::from_fn(|_| gen.next().unwrap());
        let z_i = array::from_fn(|_| gen.next().unwrap());

        Self {
            pp_digest,
            self_trace,
            paired_trace,
            step,
            z_0,
            z_i,
        }
    }
}

impl<const ARITY: usize, F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for Input<ARITY, F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            pp_digest: (pp0, pp1),
            self_trace,
            paired_trace,
            step,
            z_0,
            z_i,
        } = self;

        ro.absorb(&self_trace.input_accumulator)
            .absorb(&paired_trace.input_accumulator)
            .absorb_field(*pp0)
            .absorb_field(*pp1)
            .absorb_field(F::from(*step as u64))
            .absorb_field_iter(z_0.iter().copied())
            .absorb_field_iter(z_i.iter().copied());
    }
}

impl<const ARITY: usize, F: PrimeField> Input<ARITY, F> {
    pub(super) fn get_without_witness(&self) -> Self {
        // Zero out `pp_digest`.
        let pp_digest = (F::ZERO, F::ZERO);

        // Zero out `self_trace`.
        let self_trace = SelfTrace {
            input_accumulator: ProtoGalaxyAccumulatorInstance {
                ins: NativePlonkInstance {
                    W_commitments: vec![
                        BigUintPoint::identity();
                        self.self_trace.input_accumulator.ins.W_commitments.len()
                    ],
                    instances: self
                        .self_trace
                        .input_accumulator
                        .ins
                        .instances
                        .iter()
                        .map(|v| vec![F::ZERO; v.len()])
                        .collect(),
                    challenges: vec![
                        F::ZERO;
                        self.self_trace.input_accumulator.ins.challenges.len()
                    ],
                },
                betas: vec![F::ZERO; self.self_trace.input_accumulator.betas.len()]
                    .into_boxed_slice(),
                e: F::ZERO,
            },
            incoming: NativePlonkInstance {
                W_commitments: vec![
                    BigUintPoint::identity();
                    self.self_trace.incoming.W_commitments.len()
                ],
                instances: self
                    .self_trace
                    .incoming
                    .instances
                    .iter()
                    .map(|v| vec![F::ZERO; v.len()])
                    .collect(),
                challenges: vec![F::ZERO; self.self_trace.incoming.challenges.len()],
            },
            proof: nifs::protogalaxy::Proof {
                poly_F: UnivariatePoly::new_zeroed(self.self_trace.proof.poly_F.len()),
                poly_K: UnivariatePoly::new_zeroed(self.self_trace.proof.poly_K.len()),
            },
        };

        // Zero out `paired_trace`.
        let paired_trace = PairedTrace {
            input_accumulator: SangriaAccumulatorInstance {
                ins: PairedPlonkInstance {
                    W_commitments: vec![
                        (F::ZERO, F::ZERO);
                        self.paired_trace.input_accumulator.ins.W_commitments.len()
                    ],
                    instances: self
                        .paired_trace
                        .input_accumulator
                        .ins
                        .instances
                        .iter()
                        .map(|v| {
                            vec![BigUint::zero(DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT); v.len()]
                        })
                        .collect(),
                    challenges: vec![
                        BigUint::zero(DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT);
                        self.paired_trace.input_accumulator.ins.challenges.len()
                    ],
                },
                E_commitment: (F::ZERO, F::ZERO),
                u: F::ZERO,
            },
            incoming: self
                .paired_trace
                .incoming
                .iter()
                .map(|incoming| PairedIncoming {
                    instance: PairedPlonkInstance {
                        W_commitments: vec![
                            (F::ZERO, F::ZERO);
                            incoming.instance.W_commitments.len()
                        ],
                        instances: incoming
                            .instance
                            .instances
                            .iter()
                            .map(|v| {
                                vec![
                                    BigUint::zero(DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT);
                                    v.len()
                                ]
                            })
                            .collect(),
                        challenges: vec![
                            BigUint::zero(DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT);
                            incoming.instance.challenges.len()
                        ],
                    },
                    proof: vec![(F::ZERO, F::ZERO); incoming.proof.len()],
                })
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        };

        // Zero out `step`.
        let step = 0;

        // Zero out `z_0` and `z_i`.
        let z_0 = array::from_fn(|_| F::ZERO);
        let z_i = array::from_fn(|_| F::ZERO);

        // Construct the new zeroed Input instance.
        Self {
            pp_digest,
            self_trace,
            paired_trace,
            step,
            z_0,
            z_i,
        }
    }

    /// This method creates an input to initialize an empty accumulators and incoming traces of the
    /// correct size of fields
    pub fn new_initial<CMain: CurveAffine<ScalarExt = F>, CSup: CurveAffine<Base = F>>(
        native_plonk_structure: &plonk::PlonkStructure<CMain::ScalarExt>,
        paired_plonk_structure: &plonk::PlonkStructure<CSup::ScalarExt>,
        paired_plonk_instance: &nifs::sangria::FoldablePlonkInstance<
            CSup,
            { support_circuit::INSTANCES_LEN },
        >,
    ) -> Self {
        let self_trace = SelfTrace::new_initial(native_plonk_structure);

        Self {
            pp_digest: (F::ZERO, F::ZERO),
            paired_trace: PairedTrace::new_initial::<CSup>(
                paired_plonk_structure,
                paired_plonk_instance,
                self_trace.W_commitments_len(),
            ),
            self_trace,
            step: 0,
            z_0: array::from_fn(|_| F::ZERO),
            z_i: array::from_fn(|_| F::ZERO),
        }
    }
}

pub struct InputBuilder<
    'link,
    CMain: CurveAffine<ScalarExt = CSup::Base>,
    CSup: CurveAffine,
    const ARITY: usize,
> {
    pub pp_digest: (CSup::Base, CSup::Base),
    pub step: usize,

    pub self_acc: &'link nifs::protogalaxy::AccumulatorInstance<CMain>,
    pub self_incoming: &'link plonk::PlonkInstance<CMain>,
    pub self_proof: nifs::protogalaxy::Proof<CMain::Scalar>,

    pub paired_acc:
        &'link nifs::sangria::RelaxedPlonkInstance<CSup, { support_circuit::INSTANCES_LEN }>,
    pub paired_incoming: &'link [(
        nifs::sangria::FoldablePlonkInstance<CSup, { support_circuit::INSTANCES_LEN }>,
        nifs::sangria::CrossTermCommits<CSup>,
    )],

    pub z_0: [CMain::Scalar; ARITY],
    pub z_i: [CMain::Scalar; ARITY],
}

impl<CMain: CurveAffine<ScalarExt = CSup::Base>, CSup: CurveAffine, const ARITY: usize>
    InputBuilder<'_, CMain, CSup, ARITY>
{
    pub fn build(self) -> Input<ARITY, CMain::Scalar> {
        let Self {
            pp_digest,
            step,
            self_acc,
            self_incoming,
            self_proof,
            paired_acc,
            paired_incoming,
            z_0,
            z_i,
        } = self;

        Input {
            pp_digest,
            step,
            z_0,
            z_i,
            self_trace: SelfTrace {
                input_accumulator: ProtoGalaxyAccumulatorInstance::new(self_acc),
                incoming: NativePlonkInstance::new(self_incoming),
                proof: self_proof,
            },
            paired_trace: PairedTrace {
                input_accumulator: SangriaAccumulatorInstance::new(paired_acc),
                incoming: paired_incoming
                    .iter()
                    .map(|(instance, proof)| PairedIncoming::new(instance, proof))
                    .collect(),
            },
        }
    }
}
