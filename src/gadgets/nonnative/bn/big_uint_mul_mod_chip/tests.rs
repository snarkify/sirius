use std::{marker::PhantomData, mem};

use halo2_proofs::{
    circuit::SimpleFloorPlanner,
    plonk::{Advice, Circuit, Column, Instance},
};
use num_traits::FromPrimitive;
use tracing::*;

use super::*;
use crate::{
    ff::{PrimeField, PrimeFieldBits},
    halo2curves::pasta::Fp,
    run_mock_prover_test,
};

const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(Fp::S as usize) };
const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

mod mult_mod_tests {
    use tracing_test::traced_test;

    use super::*;

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<MAIN_GATE_T>,
        lhs: Column<Instance>,
        rhs: Column<Instance>,
        quotient: Column<Instance>,
        remainder: Column<Instance>,

        formal_lhs: Column<Advice>,
        formal_rhs: Column<Advice>,
        formal_mod: Column<Advice>,
    }

    #[derive(Debug)]
    struct TestCircuit<F: PrimeField + PrimeFieldBits> {
        modulus: BigUint<F>,
    }

    impl<F: PrimeField + PrimeFieldBits> Circuit<F> for TestCircuit<F> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            let lhs = meta.instance_column();
            meta.enable_equality(lhs);

            let rhs = meta.instance_column();
            meta.enable_equality(rhs);

            let quotient = meta.instance_column();
            meta.enable_equality(quotient);

            let remainder = meta.instance_column();
            meta.enable_equality(remainder);

            let formal_lhs = meta.advice_column();
            meta.enable_equality(formal_lhs);

            let formal_rhs = meta.advice_column();
            meta.enable_equality(formal_rhs);

            let formal_mod = meta.advice_column();
            meta.enable_equality(formal_mod);

            Config {
                lhs,
                rhs,
                quotient,
                remainder,
                formal_lhs,
                formal_rhs,
                formal_mod,
                main_gate_config: MainGate::<F, MAIN_GATE_T>::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            trace!("Start synthesize");

            let chip =
                BigUintMulModChip::<F>::new(config.main_gate_config, LIMB_WIDTH, LIMBS_COUNT);

            let (quotient, remainder): (Vec<_>, Vec<_>) = layouter
                .assign_region(
                    || "assign_mult",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        let limbs_count = LIMBS_COUNT.get();
                        let (lhs, rhs): (Vec<_>, Vec<_>) =
                            itertools::multiunzip((0..limbs_count).map(|limb_index| {
                                let res = (
                                    region
                                        .assign_advice_from_instance(
                                            || format!("lhs {limb_index}"),
                                            config.formal_lhs,
                                            config.lhs,
                                            limb_index,
                                        )
                                        .unwrap(),
                                    region
                                        .assign_advice_from_instance(
                                            || format!("rhs {limb_index}"),
                                            config.formal_rhs,
                                            config.rhs,
                                            limb_index,
                                        )
                                        .unwrap(),
                                );

                                region.next();

                                res
                            }));

                        let ModOperationResult {
                            quotient,
                            remainder,
                        } = chip
                            .mult_mod(&mut region, &lhs, &rhs, &self.modulus)
                            .unwrap();

                        Ok((quotient, remainder))
                    },
                )
                .unwrap();

            for (offset, limb) in quotient.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.quotient, offset)?;
            }

            for (offset, limb) in remainder.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.remainder, offset)?;
            }

            Ok(())
        }
    }

    struct Context {
        lhs: u128,
        rhs: u128,
        modulus: u128,
    }

    #[traced_test]
    #[test]
    fn test_mult_mod_bn() {
        const K: u32 = 11;

        let cases = [
            Context {
                lhs: 1u128,
                rhs: u128::MAX,
                modulus: 256,
            },
            Context {
                lhs: u128::MAX,
                rhs: 1,
                modulus: 256,
            },
            Context {
                lhs: u64::MAX as u128,
                rhs: u32::MAX as u128,
                modulus: 256,
            },
            Context {
                lhs: u128::MAX,
                rhs: u64::MAX as u128,
                modulus: 256,
            },
            Context {
                lhs: u128::MAX,
                rhs: 256u128,
                modulus: 512,
            },
            Context {
                lhs: u128::MAX,
                rhs: 256u128,
                modulus: 11,
            },
        ];

        for Context { lhs, rhs, modulus } in cases {
            let lhs = BigUintRaw::from_u128(lhs).unwrap();
            let rhs = BigUintRaw::from_u128(rhs).unwrap();

            let quotient = (&lhs * &rhs) / modulus;
            let remainer = (&lhs * &rhs) % modulus;

            println!("{lhs} * {rhs} = {quotient} * {modulus:?} + {remainer}");

            let lhs = BigUint::from_biguint(&lhs, LIMB_WIDTH, LIMBS_COUNT).unwrap();
            let rhs = BigUint::from_biguint(&rhs, LIMB_WIDTH, LIMBS_COUNT).unwrap();

            let quotient = BigUint::from_biguint(&quotient, LIMB_WIDTH, LIMBS_COUNT).unwrap();
            let remainer = BigUint::from_biguint(&remainer, LIMB_WIDTH, LIMBS_COUNT).unwrap();

            let public_inputs = vec![
                lhs.limbs().to_vec(),
                rhs.limbs().to_vec(),
                quotient.limbs().to_vec(),
                remainer.limbs().to_vec(),
            ];

            let modulus = BigUint::from_biguint(
                &BigUintRaw::from_u128(modulus).unwrap(),
                LIMB_WIDTH,
                LIMBS_COUNT,
            )
            .unwrap();

            run_mock_prover_test!(K, TestCircuit::<Fp> { modulus }, public_inputs);
        }
    }
}

mod components_tests {
    use halo2_proofs::circuit::Value;
    use tracing_test::traced_test;

    use super::*;

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<MAIN_GATE_T>,
        lhs: Column<Instance>,
        rhs: Column<Instance>,
        assigned_mult: Column<Instance>,
        grouped_assigned_mult: Column<Instance>,
        assigned_sum: Column<Instance>,

        advice_lhs: Column<Advice>,
        advice_rhs: Column<Advice>,
    }

    #[derive(Debug, Default)]
    struct TestCircuit<F: PrimeField + PrimeFieldBits> {
        _p: PhantomData<F>,
    }

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(Fp::S as usize) };
    const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    impl<F: PrimeField + PrimeFieldBits> Circuit<F> for TestCircuit<F> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!("without_witnesses")
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            let advice_lhs = meta.advice_column();
            meta.enable_equality(advice_lhs);

            let advice_rhs = meta.advice_column();
            meta.enable_equality(advice_rhs);

            let lhs = meta.instance_column();
            meta.enable_equality(lhs);

            let rhs = meta.instance_column();
            meta.enable_equality(rhs);

            let assigned_mult = meta.instance_column();
            meta.enable_equality(assigned_mult);

            let assigned_sum = meta.instance_column();
            meta.enable_equality(assigned_sum);

            let grouped_assigned_mult = meta.instance_column();
            meta.enable_equality(grouped_assigned_mult);

            Config {
                lhs,
                rhs,
                advice_lhs,
                advice_rhs,
                assigned_mult,
                assigned_sum,
                grouped_assigned_mult,
                main_gate_config: MainGate::<F, MAIN_GATE_T>::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            trace!("Start synthesize");

            let chip =
                BigUintMulModChip::<F>::new(config.main_gate_config, LIMB_WIDTH, LIMBS_COUNT);

            let (assigned_mult, assigned_sum, grouped_mult): (Vec<_>, Vec<_>, Vec<_>) = layouter
                .assign_region(
                    || "assign_mult",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        let limbs_count = LIMBS_COUNT.get();
                        let (lhs, rhs): (Vec<_>, Vec<_>) = (0..limbs_count)
                            .map(|limb_index| {
                                let res = (
                                    region
                                        .assign_advice_from_instance(
                                            || format!("lhs {limb_index}"),
                                            config.advice_lhs,
                                            config.lhs,
                                            limb_index,
                                        )
                                        .unwrap(),
                                    region
                                        .assign_advice_from_instance(
                                            || format!("rhs {limb_index}"),
                                            config.advice_rhs,
                                            config.rhs,
                                            limb_index,
                                        )
                                        .unwrap(),
                                );

                                region.next();

                                res
                            })
                            .unzip();

                        let max_word_without_overflow: F = big_uint::nat_to_f(
                            &big_uint::get_big_int_with_n_ones(LIMB_WIDTH.get()),
                        )
                        .unwrap_or_default();

                        let mult = chip
                            .assign_mult(
                                &mut region,
                                &lhs,
                                &rhs,
                                &max_word_without_overflow,
                                &max_word_without_overflow,
                            )
                            .unwrap();

                        let sum = chip
                            .assign_sum(
                                &mut region,
                                &OverflowingBigUint {
                                    cells: lhs.clone(),
                                    max_word: big_uint::nat_to_f::<F>(
                                        &big_uint::get_big_int_with_n_ones(LIMB_WIDTH.get()),
                                    )
                                    .unwrap_or_default(),
                                },
                                &rhs.iter()
                                    .take(limbs_count)
                                    .map(|c| *c.value().unwrap().unwrap_or(&F::ZERO))
                                    .collect::<Box<[_]>>(),
                            )
                            .unwrap();

                        let max_word_bn: BigUintRaw = big_uint::f_to_nat(&mult.res.max_word);

                        let carry_bits = calc_carry_bits(&max_word_bn, LIMB_WIDTH).unwrap();
                        let limbs_per_group =
                            calc_limbs_per_group::<F>(carry_bits, LIMB_WIDTH).unwrap();

                        let grouped_mult = chip
                            .group_limbs(&mut region, mult.res.clone(), limbs_per_group)
                            .unwrap();

                        // TODO Move to separate test
                        for bytes in [
                            u128::MAX,
                            u128::from_le_bytes((0u8..16).collect::<Vec<_>>().try_into().unwrap()),
                            0u128,
                        ] {
                            let number = F::from_u128(bytes);
                            let bits_cells = chip
                                .assign_and_check_bits(
                                    &mut region,
                                    number.to_repr().as_ref(),
                                    NonZeroUsize::new(mem::size_of::<u128>() * 8).unwrap(),
                                )
                                .unwrap();

                            if let Some(accumulated) = itertools::multizip((
                                bits_cells.iter(),
                                util::get_power_of_two_iter::<F>(),
                            ))
                            .try_fold(
                                F::ZERO,
                                |acc, (bit_cell, shift)| {
                                    Some(
                                        acc + bit_cell.value().unwrap().map(|bit| {
                                            assert!(*bit == F::ZERO || *bit == F::ONE);
                                            shift * bit
                                        })?,
                                    )
                                },
                            ) {
                                assert_eq!(accumulated, number);
                            }
                        }

                        let number = region
                            .assign_advice(
                                || "check fits in bits",
                                config.advice_lhs,
                                Value::known(F::from_u128(u32::MAX as u128)),
                            )
                            .unwrap();

                        chip.decompose_in_bits(
                            &mut region,
                            number,
                            NonZeroUsize::new(mem::size_of::<u32>() * 8).unwrap(),
                        )
                        .unwrap();

                        chip.is_equal(&mut region, mult.res.clone(), mult.res.clone())
                            .unwrap();

                        Ok((mult.res.cells, sum.res.cells, grouped_mult.cells))
                    },
                )
                .unwrap();

            for (offset, limb) in assigned_mult.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.assigned_mult, offset)?;
            }

            for (offset, limb) in assigned_sum.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.assigned_sum, offset)?;
            }

            for (offset, limb) in grouped_mult.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.grouped_assigned_mult, offset)?;
            }

            Ok(())
        }
    }

    fn mult_with_overflow<F: PrimeField>(lhs: &BigUint<F>, rhs: &BigUint<F>) -> BigUint<F> {
        let lhs_limbs_count = lhs.limbs().len();
        let rhs_limbs_count = rhs.limbs().len();

        let mut production_cells: Vec<Option<F>> =
            vec![None; lhs_limbs_count + rhs_limbs_count - 1];

        for (i, lhs_limb) in lhs.limbs().iter().enumerate() {
            for (j, rhs_limb) in rhs.limbs().iter().enumerate() {
                let k = i + j;
                production_cells[k] =
                    Some(production_cells[k].take().unwrap_or(F::ZERO) + (*lhs_limb * rhs_limb));
            }
        }

        let mut production_cells = production_cells.into_iter().flatten();

        let bn = BigUint::from_limbs(
            production_cells.by_ref().take(LIMBS_COUNT.get()),
            LIMB_WIDTH,
            LIMBS_COUNT,
        )
        .unwrap();

        // Check then limbs count not reached expected limit & all tail contains only zeroes
        assert!(production_cells.all(|limb| limb.eq(&F::ZERO)));

        bn
    }

    fn sum_with_overflow<F: PrimeField>(lhs: &BigUint<F>, rhs: &BigUint<F>) -> BigUint<F> {
        BigUint::from_limbs(
            lhs.limbs()
                .iter()
                .zip_longest(rhs.limbs().iter())
                .enumerate()
                .map(|(index, limbs)| {
                    let limb = match limbs {
                        EitherOrBoth::Both(lhs, rhs) => {
                            trace!("sum val lhs[{index}] = {lhs:?}");
                            trace!("sum val rhs[{index}] = {rhs:?}");
                            *lhs + rhs
                        }
                        EitherOrBoth::Left(lhs) => {
                            trace!("sum val rhs[{index}] = None");
                            trace!("sum val lhs[{index}] = {lhs:?}");
                            *lhs
                        }
                        EitherOrBoth::Right(rhs) => {
                            trace!("sum val rhs[{index}] = {rhs:?}");
                            trace!("sum val lhs[{index}] = None");
                            *rhs
                        }
                    };
                    trace!("calculated val res[{index}] = {limb:?}");
                    limb
                }),
            LIMB_WIDTH,
            LIMBS_COUNT,
        )
        .unwrap()
    }

    fn group_limbs<F: PrimeField>(inp: &BigUint<F>, max_word: BigUintRaw) -> BigUint<F> {
        let limbs_per_group =
            calc_limbs_per_group::<F>(calc_carry_bits(&max_word, LIMB_WIDTH).unwrap(), LIMB_WIDTH)
                .unwrap()
                .get();

        let limb_block = iter::successors(Some(F::ONE), |l| Some(l.double()))
            .nth(LIMB_WIDTH.get())
            .unwrap();

        BigUint::from_limbs(
            inp.limbs()
                .iter()
                .chunks(limbs_per_group)
                .into_iter()
                .map(|limbs_for_group| {
                    limbs_for_group
                        .zip(iter::successors(Some(F::ONE), |l| Some(limb_block * l)))
                        .map(|(limb, shift)| shift * limb)
                        .sum()
                }),
            LIMB_WIDTH,
            LIMBS_COUNT,
        )
        .unwrap()
    }

    #[traced_test]
    #[test]
    fn test_mult_mod_bn() {
        let lhs = BigUintRaw::from_u64(u64::MAX).unwrap() * BigUintRaw::from_u64(100).unwrap();
        let rhs = BigUintRaw::from_u64(u64::MAX).unwrap() * BigUintRaw::from_u64(u64::MAX).unwrap();

        let lhs = BigUint::from_biguint(&lhs, LIMB_WIDTH, LIMBS_COUNT).unwrap();
        let rhs = BigUint::from_biguint(&rhs, LIMB_WIDTH, LIMBS_COUNT).unwrap();
        let prod = mult_with_overflow(&lhs, &rhs);
        info!("prod {prod:?}");
        let sum = sum_with_overflow(&lhs, &rhs);
        info!("sum {sum:?}");

        let max_word = big_uint::get_big_int_with_n_ones(LIMB_WIDTH.get());
        let grouped = group_limbs(&prod, &max_word * &max_word);
        info!("grouped {grouped:?}");

        const K: u32 = 11;
        let ts = TestCircuit::<Fp>::default();
        run_mock_prover_test!(
            K,
            ts,
            vec![
                lhs.limbs().to_vec(),
                rhs.limbs().to_vec(),
                prod.limbs().to_vec(),
                sum.limbs().to_vec(),
                grouped.limbs().to_vec(),
            ]
        );
    }

    #[traced_test]
    #[test]
    fn test_mult_mod_zero() {
        let lhs = BigUintRaw::from_u64(u64::MAX).unwrap() * BigUintRaw::from_u64(100).unwrap();
        let rhs = BigUintRaw::from_u64(0).unwrap();

        let lhs = BigUint::from_biguint(&lhs, LIMB_WIDTH, LIMBS_COUNT).unwrap();
        let rhs = BigUint::from_biguint(&rhs, LIMB_WIDTH, LIMBS_COUNT).unwrap();
        let prod = mult_with_overflow(&lhs, &rhs);
        info!("prod {prod:?}");
        let sum = sum_with_overflow(&lhs, &rhs);
        info!("sum {sum:?}");

        let max_word = big_uint::get_big_int_with_n_ones(LIMB_WIDTH.get());
        let grouped = group_limbs(&prod, &max_word * &max_word);
        info!("grouped {grouped:?}");

        const K: u32 = 11;
        let ts = TestCircuit::<Fp>::default();
        run_mock_prover_test!(
            K,
            ts,
            vec![
                lhs.limbs().to_vec(),
                rhs.limbs().to_vec(),
                prod.limbs().to_vec(),
                sum.limbs().to_vec(),
                grouped.limbs().to_vec(),
            ]
        );
    }
}

mod red_mod_tests {
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        plonk::{Advice, Circuit, Column, Instance},
    };
    use num_traits::FromPrimitive;
    use tracing_test::traced_test;

    use super::*;
    use crate::{halo2curves::pasta::Fp, run_mock_prover_test};

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<MAIN_GATE_T>,
        val: Column<Instance>,
        quotient: Column<Instance>,
        remainder: Column<Instance>,

        formal_val: Column<Advice>,
        formal_mod: Column<Advice>,
    }

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(Fp::S as usize) };
    const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    #[derive(Debug)]
    struct TestCircuit<F: PrimeField + PrimeFieldBits> {
        modulus: BigUint<F>,
    }

    impl<F: PrimeField + PrimeFieldBits> Circuit<F> for TestCircuit<F> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            let val = meta.instance_column();
            meta.enable_equality(val);

            let quotient = meta.instance_column();
            meta.enable_equality(quotient);

            let remainder = meta.instance_column();
            meta.enable_equality(remainder);

            let formal_val = meta.advice_column();
            meta.enable_equality(formal_val);

            let formal_mod = meta.advice_column();
            meta.enable_equality(formal_mod);

            Config {
                val,
                quotient,
                remainder,
                formal_val,
                formal_mod,
                main_gate_config: MainGate::<F, MAIN_GATE_T>::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            trace!("Start synthesize");

            let chip =
                BigUintMulModChip::<F>::new(config.main_gate_config, LIMB_WIDTH, LIMBS_COUNT);

            let (quotient, remainder): (Vec<_>, Vec<_>) = layouter
                .assign_region(
                    || "assign_mult",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        let limbs_count = LIMBS_COUNT.get();
                        let val = (0..limbs_count)
                            .map(|limb_index| {
                                let res = region
                                    .assign_advice_from_instance(
                                        || format!("lhs {limb_index}"),
                                        config.formal_val,
                                        config.val,
                                        limb_index,
                                    )
                                    .unwrap();

                                region.next();

                                res
                            })
                            .collect::<Vec<_>>();

                        let ModOperationResult {
                            quotient,
                            remainder,
                        } = chip
                            .red_mod(
                                &mut region,
                                OverflowingBigUint::new(val, LIMB_WIDTH),
                                &self.modulus,
                            )
                            .unwrap();

                        Ok((quotient, remainder))
                    },
                )
                .unwrap();

            for (offset, limb) in quotient.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.quotient, offset)?;
            }

            for (offset, limb) in remainder.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.remainder, offset)?;
            }

            Ok(())
        }
    }

    struct Context {
        val: u128,
        modulus: u128,
    }

    #[traced_test]
    #[test]
    fn test_red_mod_bn() {
        const K: u32 = 11;

        let cases = [
            Context {
                val: u128::MAX,
                modulus: 256,
            },
            Context {
                val: u64::MAX as u128,
                modulus: 256,
            },
            Context {
                val: u128::MAX,
                modulus: 256,
            },
            Context {
                val: u128::MAX,
                modulus: 512,
            },
            Context {
                val: 256u128,
                modulus: 11,
            },
            Context {
                val: 0,
                modulus: 11,
            },
        ];

        for Context { val, modulus } in cases {
            let val = BigUintRaw::from_u128(val).unwrap();
            let modulus = BigUintRaw::from_u128(modulus).unwrap();

            let quotient = &val / &modulus;
            let remainer = &val % &modulus;

            println!("{val} = {quotient} * {modulus} + {remainer}");

            let val = BigUint::from_biguint(&val, LIMB_WIDTH, LIMBS_COUNT).unwrap();
            let modulus = BigUint::from_biguint(&modulus, LIMB_WIDTH, LIMBS_COUNT).unwrap();

            let quotient = BigUint::from_biguint(&quotient, LIMB_WIDTH, LIMBS_COUNT).unwrap();
            let remainer = BigUint::from_biguint(&remainer, LIMB_WIDTH, LIMBS_COUNT).unwrap();

            run_mock_prover_test!(
                K,
                TestCircuit::<Fp> { modulus },
                vec![
                    val.limbs().to_vec(),
                    quotient.limbs().to_vec(),
                    remainer.limbs().to_vec(),
                ]
            );
        }
    }
}

mod decompose_tests {
    use halo2_proofs::{arithmetic::Field, circuit::Value};
    use tracing_test::traced_test;

    use super::*;

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<MAIN_GATE_T>,
        val: Column<Instance>,
        limbs: Column<Instance>,

        formal_val: Column<Advice>,
    }

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(Fp::S as usize) };
    const LIMBS_COUNT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(5) };

    #[derive(Debug, Default)]
    struct TestCircuit<F: PrimeField + PrimeFieldBits>(PhantomData<F>);

    impl<F: PrimeField + PrimeFieldBits> Circuit<F> for TestCircuit<F> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            let val = meta.instance_column();
            meta.enable_equality(val);

            let limbs = meta.instance_column();
            meta.enable_equality(limbs);

            let formal_val = meta.advice_column();
            meta.enable_equality(formal_val);

            Config {
                val,
                limbs,
                formal_val,
                main_gate_config: MainGate::<F, MAIN_GATE_T>::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            trace!("Start synthesize");

            let config_clone = config.clone();

            let chip =
                BigUintMulModChip::<F>::new(config.main_gate_config, LIMB_WIDTH, LIMBS_COUNT);

            let limbs: Vec<_> = layouter
                .assign_region(
                    || "from_assigned_cell_to_limbs",
                    |mut region| {
                        config_clone.main_gate_config.name_columns(&mut region);

                        let mut region = RegionCtx::new(region, 0);

                        let val = region
                            .assign_advice_from_instance(|| "val", config.formal_val, config.val, 0)
                            .unwrap();

                        region.next();

                        let limbs = chip
                            .from_assigned_value_to_limbs(&mut region, &val)
                            .unwrap();

                        for val in [
                            F::from_u128(0u128),
                            F::from_u128(u128::MAX / 2),
                            F::from_u128(u128::MAX),
                            F::from_u128(u128::MAX) * F::from_u128(1_000_000_000),
                        ] {
                            region.next();

                            let new_val = region
                                .assign_advice(|| "val", config.formal_val, Value::known(val))
                                .unwrap();

                            region.next();

                            chip.from_assigned_value_to_limbs(&mut region, &new_val)
                                .unwrap();
                        }

                        Ok(limbs)
                    },
                )
                .unwrap();

            for (offset, limb) in limbs.into_iter().enumerate() {
                layouter.constrain_instance(limb.cell(), config.limbs, offset)?;
            }

            Ok(())
        }
    }

    struct Context {
        val: u128,
    }

    #[traced_test]
    #[test]
    fn test_from_assigned_cell() {
        const K: u32 = 11;
        let ts = TestCircuit::<Fp>::default();

        let cases = [
            Context { val: u128::MAX },
            Context {
                val: u64::MAX as u128,
            },
            Context { val: u128::MAX },
            Context { val: u128::MAX / 2 },
            Context { val: u128::MAX / 4 },
            Context { val: 256u128 },
            Context { val: 0 },
        ];

        for Context { val } in cases {
            let mut limbs = BigUint::from_u128(val, LIMB_WIDTH, LIMBS_COUNT)
                .unwrap()
                .limbs()
                .to_vec();
            limbs.resize(LIMBS_COUNT.get(), Fp::ZERO);

            run_mock_prover_test!(K, ts, vec![vec![Fp::from_u128(val)], limbs]);
        }
    }
}

mod to_le_bits {
    use halo2_proofs::arithmetic::Field;
    use rand::Rng;
    use tracing_test::traced_test;

    use super::*;

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<MAIN_GATE_T>,
        input: Column<Instance>,
        expected_output: Column<Instance>,
    }

    #[derive(Debug, Default)]
    struct TestCircuit<F: PrimeField + PrimeFieldBits> {
        _m: PhantomData<F>,
    }

    impl<F: PrimeField + PrimeFieldBits> Circuit<F> for TestCircuit<F> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            let input = meta.instance_column();
            meta.enable_equality(input);

            let expected_output = meta.instance_column();
            meta.enable_equality(expected_output);
            Config {
                input,
                expected_output,
                main_gate_config: MainGate::<F, MAIN_GATE_T>::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            trace!("Start synthesize");

            let config_clone = config.clone();

            let chip = BigUintMulModChip::<F>::new(
                config.main_gate_config.clone(),
                LIMB_WIDTH,
                LIMBS_COUNT,
            );

            let bits: Vec<_> = layouter
                .assign_region(
                    || "to_le_bits",
                    |mut region| {
                        config_clone.main_gate_config.name_columns(&mut region);

                        let mut region = RegionCtx::new(region, 0);

                        let assigned_limbs = (0..LIMBS_COUNT.get())
                            .zip(config.main_gate_config.state.iter().enumerate().cycle())
                            .map(|(limb_index, (column_index, column))| {
                                if column_index == 0 {
                                    region.next();
                                }

                                region.assign_advice_from_instance(
                                    || format!("limb {limb_index}"),
                                    *column,
                                    config.input,
                                    limb_index,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?;

                        region.next();

                        Ok(chip.to_le_bits(&mut region, &assigned_limbs).unwrap())
                    },
                )
                .unwrap();

            for (offset, limb) in bits.into_iter().enumerate() {
                if let Some(bit) = limb.value().unwrap().copied() {
                    debug!("on-circuit bits[{offset}] = {bit:?}");
                }

                layouter.constrain_instance(limb.cell(), config.expected_output, offset)?;
            }

            Ok(())
        }
    }

    #[traced_test]
    #[test]
    fn to_le_bits() {
        const K: u32 = 15;
        let ts = TestCircuit::<Fp>::default();

        for val in [0, u128::MAX, rand::thread_rng().gen()] {
            let mut input_limbs = BigUint::from_u128(val, LIMB_WIDTH, LIMBS_COUNT)
                .unwrap()
                .limbs()
                .to_vec();
            input_limbs.resize(LIMBS_COUNT.get(), Fp::ZERO);

            let val = val.to_le_bytes();
            let mut bits_repr = LittleEndianReader::new(&val);
            let expected_bits = iter::repeat_with(|| bits_repr.read_bit())
                .map(|b| b.unwrap_or(false))
                .take(LIMB_WIDTH.get() * LIMBS_COUNT.get())
                .enumerate()
                .map(|(i, bit)| {
                    debug!("off-circuit bits[{i}] = {bit:?}");
                    Fp::from(bit)
                })
                .collect::<Vec<_>>();

            run_mock_prover_test!(K, ts, vec![input_limbs, expected_bits]);
        }
    }
}
