use super::*;

mod mult_mod_tests {
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Advice, Circuit, Column, Instance},
    };
    use halo2curves::pasta::Fp;
    use num_traits::FromPrimitive;

    use super::*;

    #[derive(Clone)]
    struct Config {
        main_gate_config: MainGateConfig<MAIN_GATE_T>,
        lhs: Column<Instance>,
        rhs: Column<Instance>,
        module: Column<Instance>,
        quotient: Column<Instance>,
        remainder: Column<Instance>,

        formal_lhs: Column<Advice>,
        formal_rhs: Column<Advice>,
        formal_mod: Column<Advice>,
    }

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(Fp::S as usize) };
    const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    #[derive(Debug, Default)]
    struct TestCircuit<F: ff::PrimeField + ff::PrimeFieldBits>(PhantomData<F>);

    impl<F: ff::PrimeField + ff::PrimeFieldBits> Circuit<F> for TestCircuit<F> {
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

            let module = meta.instance_column();
            meta.enable_equality(module);

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
                module,
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
                BigNatMulModChip::<F>::new(config.main_gate_config, LIMB_WIDTH, LIMBS_COUNT_LIMIT);

            let (quotient, remainder): (Vec<_>, Vec<_>) = layouter
                .assign_region(
                    || "assign_mult",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        let limbs_count_limit = LIMBS_COUNT_LIMIT.get();
                        let (lhs, rhs, module): (Vec<_>, Vec<_>, Vec<_>) =
                            itertools::multiunzip((0..limbs_count_limit).map(|limb_index| {
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
                                    region
                                        .assign_advice_from_instance(
                                            || format!("mod {limb_index}"),
                                            config.formal_mod,
                                            config.module,
                                            limb_index,
                                        )
                                        .unwrap(),
                                );

                                region.next();

                                res
                            }));

                        let MultModResult {
                            quotient,
                            remainder,
                        } = chip.mult_mod(&mut region, &lhs, &rhs, &module).unwrap();

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

    #[test_log::test]
    fn test_mult_mod_bn() {
        const K: u32 = 11;
        let ts = TestCircuit::<Fp>::default();

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
            let lhs = BigInt::from_u128(lhs).unwrap();
            let rhs = BigInt::from_u128(rhs).unwrap();
            let modulus = BigInt::from_u128(modulus).unwrap();

            let quotient = (&lhs * &rhs) / &modulus;
            let remainer = (&lhs * &rhs) % &modulus;

            println!("{lhs} * {rhs} = {quotient} * {modulus} + {remainer}");

            let lhs = BigNat::from_bigint(&lhs, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();
            let rhs = BigNat::from_bigint(&rhs, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();
            let modulus = BigNat::from_bigint(&modulus, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();

            let quotient = BigNat::from_bigint(&quotient, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();
            let remainer = BigNat::from_bigint(&remainer, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();

            let prover = match MockProver::run(
                K,
                &ts,
                vec![
                    lhs.limbs().to_vec(),
                    rhs.limbs().to_vec(),
                    modulus.limbs().to_vec(),
                    quotient.limbs().to_vec(),
                    remainer.limbs().to_vec(),
                ],
            ) {
                Ok(prover) => prover,
                Err(e) => panic!("{:?}", e),
            };
            assert_eq!(prover.verify(), Ok(()));
        }
    }
}

mod components_tests {
    use std::{marker::PhantomData, mem};

    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Advice, Circuit, Column, Instance},
    };
    use halo2curves::pasta::Fp;
    use num_traits::FromPrimitive;

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
    struct TestCircuit<F: ff::PrimeField + ff::PrimeFieldBits> {
        _p: PhantomData<F>,
    }

    const LIMB_WIDTH: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(Fp::S as usize) };
    const LIMBS_COUNT_LIMIT: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(10) };

    impl<F: ff::PrimeField + ff::PrimeFieldBits> Circuit<F> for TestCircuit<F> {
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
                BigNatMulModChip::<F>::new(config.main_gate_config, LIMB_WIDTH, LIMBS_COUNT_LIMIT);

            let (assigned_mult, assigned_sum, grouped_mult): (Vec<_>, Vec<_>, Vec<_>) = layouter
                .assign_region(
                    || "assign_mult",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        let limbs_count_limit = LIMBS_COUNT_LIMIT.get();
                        let (lhs, rhs): (Vec<_>, Vec<_>) = (0..limbs_count_limit)
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

                        let max_word_without_overflow: F =
                            big_nat::nat_to_f(&big_nat::get_big_int_with_n_ones(LIMB_WIDTH.get()))
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
                                &OverflowingBigNat {
                                    cells: lhs.clone(),
                                    max_word: big_nat::nat_to_f::<F>(
                                        &big_nat::get_big_int_with_n_ones(LIMB_WIDTH.get()),
                                    )
                                    .unwrap_or_default(),
                                },
                                &rhs.iter()
                                    .take(limbs_count_limit)
                                    .map(|c| *c.value().unwrap().unwrap_or(&F::ZERO))
                                    .collect::<Box<[_]>>(),
                            )
                            .unwrap();

                        let grouped_mult = chip.group_limbs(&mut region, mult.res.clone()).unwrap();

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
                                get_power_of_two_iter::<F>(),
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

                        chip.check_fits_in_bits(
                            &mut region,
                            number,
                            NonZeroUsize::new(mem::size_of::<u32>() * 8).unwrap(),
                        )
                        .unwrap();

                        chip.is_equal(&mut region, grouped_mult.clone(), grouped_mult.clone())
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

    fn mult_with_overflow<F: PrimeField>(lhs: &BigNat<F>, rhs: &BigNat<F>) -> BigNat<F> {
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

        BigNat::from_limbs(production_cells.into_iter().flatten(), LIMB_WIDTH).unwrap()
    }

    fn sum_with_overflow<F: PrimeField>(lhs: &BigNat<F>, rhs: &BigNat<F>) -> BigNat<F> {
        BigNat::from_limbs(
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
        )
        .unwrap()
    }

    fn group_limbs<F: PrimeField>(inp: &BigNat<F>, max_word: BigInt) -> BigNat<F> {
        let limb_width = LIMB_WIDTH.get();
        let limbs_per_group =
            calc_limbs_per_group::<F>(calc_carry_bits(&max_word, limb_width).unwrap(), limb_width)
                .unwrap();

        let limb_block = iter::successors(Some(F::ONE), |l| Some(l.double()))
            .nth(limb_width)
            .unwrap();

        BigNat::from_limbs(
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
        )
        .unwrap()
    }

    #[test_log::test]
    fn test_bn() {
        let lhs = BigInt::from_u64(u64::MAX).unwrap() * BigInt::from_u64(100).unwrap();
        let rhs = BigInt::from_u64(u64::MAX).unwrap() * BigInt::from_u64(u64::MAX).unwrap();

        let lhs = BigNat::from_bigint(&lhs, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();
        let rhs = BigNat::from_bigint(&rhs, LIMB_WIDTH, LIMBS_COUNT_LIMIT).unwrap();
        let prod = mult_with_overflow(&lhs, &rhs);
        log::info!("prod {prod:?}");
        let sum = sum_with_overflow(&lhs, &rhs);
        log::info!("sum {sum:?}");

        let max_word = big_nat::get_big_int_with_n_ones(LIMB_WIDTH.get());
        let grouped = group_limbs(&prod, &max_word * &max_word);
        log::info!("grouped {grouped:?}");

        const K: u32 = 11;
        let ts = TestCircuit::<Fp>::default();
        let prover = match MockProver::run(
            K,
            &ts,
            vec![
                lhs.limbs().to_vec(),
                rhs.limbs().to_vec(),
                prod.limbs().to_vec(),
                sum.limbs().to_vec(),
                grouped.limbs().to_vec(),
            ],
        ) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
