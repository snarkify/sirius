use std::array;

use crate::{
    gadgets::nonnative::bn::big_uint::BigUint,
    halo2_proofs::halo2curves::{ff::PrimeField, CurveAffine},
    nifs, plonk,
    polynomial::univariate::UnivariatePoly,
    prelude::{DEFAULT_LIMBS_COUNT_LIMIT, DEFAULT_LIMB_WIDTH},
};

#[derive(Clone)]
pub struct BigUintPoint<F: PrimeField> {
    x: BigUint<F>,
    y: BigUint<F>,
}

impl<C: CurveAffine> From<&C> for BigUintPoint<C::ScalarExt> {
    fn from(_value: &C) -> Self {
        todo!()
    }
}

impl<F: PrimeField> BigUintPoint<F> {
    fn identity() -> Self {
        todo!()
    }
}

#[derive(Clone)]
pub struct NativePlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<BigUintPoint<F>>,
    pub(crate) instances: Vec<Vec<F>>,
    pub(crate) challenges: Vec<F>,
}

#[derive(Clone)]
pub struct PairedPlonkInstance<F: PrimeField> {
    pub(crate) W_commitments: Vec<(F, F)>,
    pub(crate) instances: Vec<Vec<BigUint<F>>>,
    pub(crate) challenges: Vec<BigUint<F>>,
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

#[derive(Clone)]
pub struct ProtoGalaxyAccumulatorInstance<F: PrimeField> {
    pub(crate) ins: NativePlonkInstance<F>,
    pub(crate) betas: Box<[F]>,
    pub(crate) e: F,
}

/// Recursive trace of the circuit itself
pub struct SelfTrace<F: PrimeField> {
    pub input_accumulator: ProtoGalaxyAccumulatorInstance<F>,
    pub incoming: NativePlonkInstance<F>,
    pub proof: nifs::protogalaxy::Proof<F>,
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

pub struct SangriaAccumulatorInstance<F: PrimeField> {
    pub(crate) ins: PairedPlonkInstance<F>,
    pub(crate) E_commitment: (F, F),
    pub(crate) u: BigUint<F>,
}

pub struct PairedTrace<F: PrimeField> {
    pub input_accumulator: SangriaAccumulatorInstance<F>,
    // The size from one to three
    // Depdend on `W_commitments_len`
    pub incoming: Box<[PairedPlonkInstance<F>]>,
    proof: nifs::sangria::CrossTermCommits<(F, F)>,
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
