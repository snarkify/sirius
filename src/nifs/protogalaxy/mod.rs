use std::{iter, marker::PhantomData};

use ff::{Field, PrimeField};
use halo2_proofs::arithmetic::CurveAffine;
use tracing::*;

use super::*;
use crate::{
    commitment::CommitmentKey,
    constants::NUM_CHALLENGE_BITS,
    plonk::{
        PlonkStructure, PlonkTrace, RelaxedPlonkInstance, RelaxedPlonkTrace, RelaxedPlonkTraceArgs,
    },
    polynomial::univariate::UnivariatePoly,
    util,
};

pub(crate) mod poly;

/// ProtoGalaxy: Non Interactive Folding Scheme that implements main protocol defined in paper
/// [protogalaxy](https://eprint.iacr.org/2023/1106)
#[derive(Clone, Debug)]
pub struct ProtoGalaxy<const L: usize, C: CurveAffine> {
    _marker: PhantomData<C>,
}

impl<const L: usize, C: CurveAffine> ProtoGalaxy<L, C> {
    #[instrument(skip_all)]
    pub(crate) fn generate_challenge<'i>(
        pp_digest: &C,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &RelaxedPlonkInstance<C>,
        instances: impl Iterator<Item = &'i PlonkInstance<C>>,
    ) -> <C as CurveAffine>::ScalarExt {
        ro_acc
            .absorb_point(pp_digest)
            .absorb(accumulator)
            .absorb_iter(instances)
            .squeeze::<C>(NUM_CHALLENGE_BITS)
    }

    fn get_count_of_valuation(S: &PlonkStructure<C::ScalarExt>) -> usize {
        let count_of_rows = 2usize.pow(S.k as u32);
        let count_of_gates = S.gates.len();

        count_of_rows * count_of_gates
    }

    pub(crate) fn new_accumulator(
        args: AccumulatorArgs,
        params: &ProtoGalaxyProverParam<C>,
        ro_acc: &mut impl ROTrait<C::Base>,
    ) -> Accumulator<C> {
        let mut accumulator = Accumulator::new(args, Self::get_count_of_valuation(&params.S));

        let beta = Self::generate_challenge(
            &params.pp_digest,
            ro_acc,
            &accumulator.trace.U,
            iter::empty(),
        );

        accumulator
            .betas
            .iter_mut()
            .zip(iter::successors(Some(beta), |acc| Some(acc.double())))
            .for_each(|(b, beta_pow)| *b = beta_pow);

        accumulator
    }
}

pub struct ProtoGalaxyProverParam<C: CurveAffine> {
    pub(crate) S: PlonkStructure<C::ScalarExt>,
    /// digest of public parameter of IVC circuit
    pp_digest: C,
}

pub struct ProtoGalaxyProof<F: PrimeField> {
    // TODO: add comments
    pub poly_F: UnivariatePoly<F>,
    pub poly_K: UnivariatePoly<F>,
}

pub type AccumulatorArgs = RelaxedPlonkTraceArgs;

pub struct Accumulator<C: CurveAffine> {
    betas: Box<[C::ScalarExt]>,
    trace: RelaxedPlonkTrace<C>,
    e: C::ScalarExt,
}

impl<C: CurveAffine> Accumulator<C> {
    fn new(args: AccumulatorArgs, count_of_evaluation: usize) -> Self {
        Self {
            betas: vec![C::ScalarExt::ZERO; count_of_evaluation].into_boxed_slice(),
            e: C::ScalarExt::ZERO,
            trace: RelaxedPlonkTrace::new(args),
        }
    }

    fn fold(&self, _gamma: C::ScalarExt) -> Self {
        todo!()
    }
}

//impl<C: CurveAffine> Accumulator<C> {
//    fn new(num_io: usize, num_challenges: usize, num_witness: usize) -> Self {
//        Self {
//            beta: C::ScalarExt::ZERO,
//            trace: RelaxedPlonkTrace {
//                U: RelaxedPlonkInstance::new(num_io, num_challenges, num_witness),
//                W: RelaxedPlonkWitness::new(k_table_size, round_sized),
//            },
//        }
//    }
//}

impl<C: CurveAffine, const L: usize> FoldingScheme<C, L> for ProtoGalaxy<L, C> {
    type ProverParam = ProtoGalaxyProverParam<C>;
    type VerifierParam = C;
    type Accumulator = Accumulator<C>;
    type AccumulatorInstance = RelaxedPlonkInstance<C>;
    type Proof = ProtoGalaxyProof<C::ScalarExt>;

    fn setup_params(
        pp_digest: C,
        S: PlonkStructure<C::ScalarExt>,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        Ok((ProtoGalaxyProverParam { S, pp_digest }, pp_digest))
    }

    // TODO: if this function turned out to be the same, consider move to trait
    fn generate_plonk_trace(
        ck: &CommitmentKey<C>,
        instance: &[C::ScalarExt],
        witness: &[Vec<C::ScalarExt>],
        pp: &Self::ProverParam,
        ro_nark: &mut impl ROTrait<C::Base>,
    ) -> Result<PlonkTrace<C>, Error> {
        Ok(pp
            .S
            .run_sps_protocol(ck, instance, witness, ro_nark, pp.S.num_challenges)?)
    }

    fn prove(
        _ck: &CommitmentKey<C>,
        pp: &Self::ProverParam,
        ro_acc: &mut impl ROTrait<C::Base>,
        accumulator: &Self::Accumulator,
        incoming: &[PlonkTrace<C>; L],
    ) -> Result<(Self::Accumulator, Self::Proof), Error> {
        let delta = Self::generate_challenge(
            &pp.pp_digest,
            ro_acc,
            &accumulator.trace.U,
            incoming.iter().map(|t| &t.u),
        );

        let poly_F = poly::compute_F::<C::ScalarExt>(
            accumulator.betas.iter().copied(),
            delta,
            &pp.S,
            &accumulator.trace,
        )?;

        let alpha = ro_acc
            .absorb_field_iter(
                poly_F
                    .iter()
                    .map(|v| util::fe_to_fe::<C::ScalarExt, C::Base>(v).unwrap()),
            )
            .squeeze::<C>(NUM_CHALLENGE_BITS);

        let challenges = poly::PolyChallenges {
            betas: accumulator.betas.clone(),
            delta,
            alpha,
        };
        let poly_K = poly::compute_K::<C::ScalarExt>(
            &pp.S,
            alpha,
            challenges,
            &accumulator.trace,
            incoming,
        )?;

        let gamma = ro_acc
            .absorb_field_iter(poly_K.iter().map(|v| util::fe_to_fe(v).unwrap()))
            .squeeze::<C>(NUM_CHALLENGE_BITS);

        Ok((accumulator.fold(gamma), ProtoGalaxyProof { poly_F, poly_K }))
    }

    fn verify(
        _vp: &Self::VerifierParam,
        _ro_nark: &mut impl ROTrait<C::Base>,
        _ro_acc: &mut impl ROTrait<C::Base>,
        _accumulator: &Self::AccumulatorInstance,
        _incoming: &[PlonkInstance<C>; L],
        _proof: &Self::Proof,
    ) -> Result<Self::AccumulatorInstance, Error> {
        todo!()
    }
}
