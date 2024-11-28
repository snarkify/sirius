use std::array;

use super::super::{DEFAULT_LIMBS_COUNT_LIMIT, DEFAULT_LIMB_WIDTH};
use crate::{
    gadgets::nonnative::bn::big_uint::BigUint,
    halo2_proofs::halo2curves::{ff::PrimeField, CurveAffine},
    nifs, plonk,
    polynomial::univariate::UnivariatePoly,
    poseidon::{AbsorbInRO, ROTrait},
};

pub mod assigned;

#[derive(Debug, Clone)]
pub struct BigUintPoint<F: PrimeField> {
    x: BigUint<F>,
    y: BigUint<F>,
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for BigUintPoint<F> {
    fn absorb_into(&self, ro: &mut RO) {
        ro.absorb_field_iter(self.x.limbs().iter().chain(self.y.limbs().iter()).cloned());
    }
}

impl<C: CurveAffine> From<&C> for BigUintPoint<C::ScalarExt> {
    fn from(value: &C) -> Self {
        let c = value.coordinates().unwrap();
        Self {
            x: BigUint::from_different_field(c.x(), DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT_LIMIT)
                .unwrap(),
            y: BigUint::from_different_field(c.y(), DEFAULT_LIMB_WIDTH, DEFAULT_LIMBS_COUNT_LIMIT)
                .unwrap(),
        }
    }
}

impl<F: PrimeField> BigUintPoint<F> {
    fn identity() -> Self {
        Self {
            x: BigUint::zero(DEFAULT_LIMB_WIDTH),
            y: BigUint::zero(DEFAULT_LIMB_WIDTH),
        }
    }
}

#[derive(Debug, Clone)]
pub struct NativePlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<BigUintPoint<F>>,
    pub(crate) instances: Vec<Vec<F>>,
    pub(crate) challenges: Vec<F>,
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
            W_commitments: value.W_commitments.iter().map(BigUintPoint::from).collect(),
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
            W_commitments: vec![BigUintPoint::identity(); W_commitments_len],
            instances: native_plonk_structure
                .num_io
                .iter()
                .map(|len| vec![F::ZERO; *len])
                .collect(),
            challenges: vec![F::ZERO; challenges_len],
        };
        let betas_len = nifs::protogalaxy::poly::get_count_of_valuation(native_plonk_structure)
            .unwrap()
            .get();
        let proof_len = betas_len.ilog2() as usize;

        SelfTrace {
            input_accumulator: ProtoGalaxyAccumulatorInstance {
                ins: ins.clone(),
                betas: vec![F::ZERO; betas_len].into_boxed_slice(),
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
    pub(crate) u: BigUint<F>,
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for SangriaAccumulatorInstance<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            ins,
            E_commitment: (ex, ey),
            u,
        } = self;

        ro.absorb(ins).absorb_field(*ex).absorb_field(*ey).absorb(u);
    }
}

#[derive(Debug, Clone)]
pub struct PairedTrace<F: PrimeField> {
    pub input_accumulator: SangriaAccumulatorInstance<F>,
    // The size from one to three
    // Depdend on `W_commitments_len`
    pub incoming: Box<[PairedPlonkInstance<F>]>,
    proof: nifs::sangria::CrossTermCommits<(F, F)>,
}

impl<F: PrimeField, RO: ROTrait<F>> AbsorbInRO<F, RO> for PairedTrace<F> {
    fn absorb_into(&self, ro: &mut RO) {
        let Self {
            input_accumulator,
            incoming,
            proof,
        } = self;

        let proof_iter = proof.iter().flat_map(|(a, b)| [a, b]).copied();

        ro.absorb(input_accumulator)
            .absorb_iter(incoming.iter())
            .absorb_field_iter(proof_iter);
    }
}

impl<F: PrimeField> PairedTrace<F> {
    pub fn new_initial<CSup: CurveAffine<Base = F>>(
        paired_plonk_structure: &plonk::PlonkStructure<CSup::ScalarExt>,
        paired_plonk_instance: &nifs::sangria::FoldablePlonkInstance<CSup>,
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
                                DEFAULT_LIMBS_COUNT_LIMIT,
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
                    BigUint::from_different_field(
                        value,
                        DEFAULT_LIMB_WIDTH,
                        DEFAULT_LIMBS_COUNT_LIMIT,
                    )
                    .unwrap()
                })
                .collect(),
        };

        Self {
            input_accumulator: SangriaAccumulatorInstance {
                ins: ins.clone(),
                E_commitment: (F::ZERO, F::ZERO),
                u: BigUint::zero(DEFAULT_LIMB_WIDTH),
            },
            incoming: vec![ins.clone(); W_commitments_len].into_boxed_slice(),
            proof: vec![
                (F::ZERO, F::ZERO);
                paired_plonk_structure
                    .get_degree_for_folding()
                    .saturating_sub(1)
            ],
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
            BigUint::from_limbs(
                gen.by_ref().take(DEFAULT_LIMBS_COUNT_LIMIT.get()),
                DEFAULT_LIMB_WIDTH,
                DEFAULT_LIMBS_COUNT_LIMIT,
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
                        x: random_big_uint(&mut gen),
                        y: random_big_uint(&mut gen),
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
                    x: random_big_uint(&mut gen),
                    y: random_big_uint(&mut gen),
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
                    instances: vec![
                        vec![random_big_uint(&mut gen); 10]; // 5 instances each with 10 BigUint<F>
                        1
                    ],
                    challenges: vec![random_big_uint(&mut gen); 1],
                },
                E_commitment: (gen.next().unwrap(), gen.next().unwrap()),
                u: random_big_uint(&mut gen),
            },
            incoming: vec![
                PairedPlonkInstance {
                    W_commitments: vec![(gen.next().unwrap(), gen.next().unwrap()); 1],
                    instances: vec![vec![random_big_uint(&mut gen); 1]; 2],
                    challenges: vec![random_big_uint(&mut gen); 2],
                };
                1
            ]
            .into_boxed_slice(),
            proof: vec![(gen.next().unwrap(), gen.next().unwrap()); 1],
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
        todo!()
    }

    /// This method creates an input to initialize an empty accumulators and incoming traces of the
    /// correct size of fields
    pub fn new_initial<CMain: CurveAffine<ScalarExt = F>, CSup: CurveAffine<Base = F>>(
        native_plonk_structure: &plonk::PlonkStructure<CMain::ScalarExt>,
        paired_plonk_structure: &plonk::PlonkStructure<CSup::ScalarExt>,
        paired_plonk_instance: &nifs::sangria::FoldablePlonkInstance<CSup>,
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

    pub fn new<CMain: CurveAffine<ScalarExt = F>, CSup: CurveAffine<Base = F>>(
        _pp_digest: CSup,
        _native_acc: &nifs::protogalaxy::AccumulatorInstance<CMain>,
        _native_incoming: &plonk::PlonkInstance<CMain>,
        _paired_acc: &nifs::sangria::FoldablePlonkInstance<CSup>,
        _paired_incoming: &nifs::sangria::FoldablePlonkInstance<CSup>,
    ) -> Self {
        todo!()
    }
}
