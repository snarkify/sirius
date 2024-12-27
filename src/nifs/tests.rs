use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{self, Advice, Circuit, Column, ConstraintSystem, Instance, Selector},
    poly::Rotation,
};

use crate::{ff::PrimeField, halo2curves::group::ff::FromUniformBytes};

pub(crate) mod random_linear_combination_circuit {
    use super::*;
    use crate::main_gate::{MainGate, MainGateConfig, RegionCtx};

    const T: usize = 3;

    #[derive(Clone, Debug)]
    pub struct TestCircuitConfig {
        pconfig: MainGateConfig<T>,
        instance: Column<Instance>,
    }

    pub struct RandomLinearCombinationCircuit<F: PrimeField> {
        inputs: Vec<F>,
        r: F,
    }

    impl<F: PrimeField> RandomLinearCombinationCircuit<F> {
        pub fn new(inputs: Vec<F>, r: F) -> Self {
            Self { inputs, r }
        }
    }

    impl<F: PrimeField + FromUniformBytes<64>> Circuit<F> for RandomLinearCombinationCircuit<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                inputs: Vec::new(),
                r: F::ZERO,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let instance = meta.instance_column();
            meta.enable_equality(instance);

            Self::Config {
                pconfig: MainGate::configure(meta),
                instance,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), plonk::Error> {
            let pchip = MainGate::new(config.pconfig);
            let output = layouter.assign_region(
                || "test",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    pchip.random_linear_combination(ctx, self.inputs.clone(), self.r)
                },
            )?;
            layouter.constrain_instance(output.cell(), config.instance, 0)?;
            Ok(())
        }
    }
}

// test multiple gates without lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
pub(crate) mod fibo_circuit {
    use super::*;

    #[derive(Clone)]
    struct Number<F: PrimeField>(AssignedCell<F, F>);

    #[derive(Debug, Clone)]
    pub struct FiboConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        selector: Selector,
        instance: Column<Instance>,
    }

    struct FiboChip<F: PrimeField> {
        config: FiboConfig,
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField> FiboChip<F> {
        fn construct(config: FiboConfig) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: [Column<Advice>; 2],
            selector: Selector,
            instance: Column<Instance>,
        ) -> FiboConfig {
            let a = advice[0];
            let b = advice[1];

            meta.enable_equality(b);
            meta.enable_equality(instance);

            meta.create_gate("fibo-block", |meta| {
                let s = meta.query_selector(selector);
                let a1 = meta.query_advice(a, Rotation::prev());
                let b1 = meta.query_advice(b, Rotation::prev());
                let a2 = meta.query_advice(a, Rotation::cur());
                let b2 = meta.query_advice(b, Rotation::cur());
                vec![
                    s.clone() * (a2.clone() - b1.clone() - a1),
                    s * (b2 - a2 - b1),
                ]
            });

            FiboConfig {
                a,
                b,
                selector,
                instance,
            }
        }

        fn load(
            &self,
            mut layouter: impl Layouter<F>,
            a: F,
            b: F,
            nrows: usize,
        ) -> Result<(Number<F>, Number<F>), plonk::Error> {
            layouter.assign_region(
                || "entire block",
                |mut region| {
                    // assign first row
                    let mut a = region
                        .assign_advice(|| "a", self.config.a, 0, || Value::known(a))
                        .map(Number)?;

                    let mut b = region
                        .assign_advice(|| "b", self.config.b, 0, || Value::known(b))
                        .map(Number)?;

                    for idx in 1..nrows {
                        self.config.selector.enable(&mut region, idx)?;
                        let a2 = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));
                        let b2 = a2.and_then(|a| b.0.value().map(|b| a + *b));

                        a = region
                            .assign_advice(|| "a", self.config.a, idx, || a2)
                            .map(Number)?;

                        b = region
                            .assign_advice(|| "b", self.config.b, idx, || b2)
                            .map(Number)?;
                    }

                    Ok((a, b))
                },
            )
        }

        fn expose_public(
            &self,
            mut layouter: impl Layouter<F>,
            num: Number<F>,
            row: usize,
        ) -> Result<(), plonk::Error> {
            layouter.constrain_instance(num.0.cell(), self.config.instance, row)
        }
    }

    #[derive(Default)]
    pub struct FiboCircuit<F> {
        pub a: F,
        pub b: F,
        pub num: usize,
    }

    impl<F: PrimeField> Circuit<F> for FiboCircuit<F> {
        type Config = FiboConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = [meta.advice_column(), meta.advice_column()];
            let selector = meta.selector();
            let instance = meta.instance_column();

            FiboChip::configure(meta, advice, selector, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), plonk::Error> {
            let chip = FiboChip::construct(config);
            let nrows = (self.num + 1) / 2;
            let (_, b) = chip.load(layouter.namespace(|| "block"), self.a, self.b, nrows)?;
            chip.expose_public(layouter.namespace(|| "expose b"), b, 0)?;
            Ok(())
        }
    }

    pub fn get_fibo_seq(a: u64, b: u64, num: usize) -> Vec<u64> {
        let mut seq = vec![0; num];
        seq[0] = a;
        seq[1] = b;
        for i in 2..num {
            seq[i] = seq[i - 1] + seq[i - 2];
        }
        seq
    }
}

// test vector lookup
// test example adapted from https://github.com/icemelon/halo2-tutorial
pub(crate) mod fibo_circuit_with_lookup {
    use halo2_proofs::{circuit::Chip, plonk::TableColumn};
    use num_bigint::BigUint as BigUintRaw;

    use super::*;

    pub fn f_to_u64<F: PrimeField>(f: &F) -> u64 {
        BigUintRaw::from_bytes_le(f.to_repr().as_ref())
            .try_into()
            .unwrap()
    }

    #[derive(Clone, Debug)]
    struct Number<F: PrimeField>(AssignedCell<F, F>);

    #[derive(Debug, Clone)]
    pub struct FiboConfigWithLookup {
        advice: [Column<Advice>; 3],
        s_add: Selector,
        s_xor: Selector,
        xor_table: [TableColumn; 3],
        pub instance: Column<Instance>,
    }

    pub struct FiboChip<F: PrimeField> {
        pub config: FiboConfigWithLookup,
        _marker: PhantomData<F>,
    }

    // ANCHOR: chip-impl
    impl<F: PrimeField> Chip<F> for FiboChip<F> {
        type Config = FiboConfigWithLookup;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }
    // ANCHOR_END: chip-impl

    impl<F: PrimeField> FiboChip<F> {
        fn construct(config: FiboConfigWithLookup) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: [Column<Advice>; 3],
            selector: [Selector; 2],
        ) -> FiboConfigWithLookup {
            let s_add = selector[0];
            let s_xor = selector[1];

            let xor_table = [
                meta.lookup_table_column(),
                meta.lookup_table_column(),
                meta.lookup_table_column(),
            ];

            meta.enable_equality(advice[0]);
            meta.enable_equality(advice[1]);
            meta.enable_equality(advice[2]);

            meta.lookup("xor", |meta| {
                let s_xor = meta.query_selector(s_xor);
                let lhs = meta.query_advice(advice[0], Rotation::cur());
                let rhs = meta.query_advice(advice[1], Rotation::cur());
                let out = meta.query_advice(advice[2], Rotation::cur());
                vec![
                    (s_xor.clone() * lhs, xor_table[0]),
                    (s_xor.clone() * rhs, xor_table[1]),
                    (s_xor * out, xor_table[2]),
                ]
            });

            meta.create_gate("add", |meta| {
                let s_add = meta.query_selector(s_add);
                let lhs = meta.query_advice(advice[0], Rotation::cur());
                let rhs = meta.query_advice(advice[1], Rotation::cur());
                let out = meta.query_advice(advice[2], Rotation::cur());
                vec![s_add * (lhs + rhs - out)]
            });

            let instance = meta.instance_column();
            meta.enable_equality(instance);

            FiboConfigWithLookup {
                advice,
                s_add,
                s_xor,
                xor_table,
                instance,
            }
        }

        fn load_private(
            &self,
            mut layouter: impl Layouter<F>,
            a: F,
            b: F,
            c: F,
        ) -> Result<(Number<F>, Number<F>, Number<F>), plonk::Error> {
            let config = self.config();

            layouter.assign_region(
                || "private",
                |mut region| {
                    let a_num = region
                        .assign_advice(|| "a", config.advice[0], 0, || Value::known(a))
                        .map(Number)?;

                    let b_num = region
                        .assign_advice(|| "b", config.advice[1], 0, || Value::known(b))
                        .map(Number)?;

                    let c_num = region
                        .assign_advice(|| "c", config.advice[2], 0, || Value::known(c))
                        .map(Number)?;

                    Ok((a_num, b_num, c_num))
                },
            )
        }

        fn add(
            &self,
            mut layouter: impl Layouter<F>,
            a: &Number<F>,
            b: &Number<F>,
        ) -> Result<Number<F>, plonk::Error> {
            let config = self.config();
            layouter.assign_region(
                || "add",
                |mut region| {
                    config.s_add.enable(&mut region, 0)?;

                    a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                    b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                    let value = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));

                    region
                        .assign_advice(|| "out", config.advice[2], 0, || value)
                        .map(Number)
                },
            )
        }

        fn xor(
            &self,
            mut layouter: impl Layouter<F>,
            a: &Number<F>,
            b: &Number<F>,
        ) -> Result<Number<F>, plonk::Error> {
            let config = self.config();
            layouter.assign_region(
                || "xor",
                |mut region| {
                    config.s_xor.enable(&mut region, 0)?;

                    a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                    b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                    let value = a.0.value().and_then(|a| {
                        b.0.value().map(|b| {
                            let a_val = f_to_u64(a);
                            let b_val = f_to_u64(b);
                            F::from(a_val ^ b_val)
                        })
                    });

                    region
                        .assign_advice(|| "out", config.advice[2], 0, || value)
                        .map(Number)
                },
            )
        }

        fn load_table(&self, mut layouter: impl Layouter<F>) -> Result<(), plonk::Error> {
            layouter.assign_table(
                || "xor",
                |mut table| {
                    let mut idx = 0;
                    for lhs in 0..5 {
                        for rhs in 0..5 {
                            table.assign_cell(
                                || "lhs",
                                self.config.xor_table[0],
                                idx,
                                || Value::known(F::from(lhs)),
                            )?;
                            table.assign_cell(
                                || "rhs",
                                self.config.xor_table[1],
                                idx,
                                || Value::known(F::from(rhs)),
                            )?;
                            table.assign_cell(
                                || "lhs ^ rhs",
                                self.config.xor_table[2],
                                idx,
                                || Value::known(F::from(lhs ^ rhs)),
                            )?;
                            idx += 1;
                        }
                    }
                    Ok(())
                },
            )
        }
    }

    #[derive(Default)]
    pub struct FiboCircuitWithLookup<F> {
        pub a: F,
        pub b: F,
        pub c: F,
        pub num: usize,
    }

    impl<F: PrimeField> Circuit<F> for FiboCircuitWithLookup<F> {
        type Config = FiboConfigWithLookup;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];
            let selector = [meta.selector(), meta.complex_selector()];
            FiboChip::configure(meta, advice, selector)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), plonk::Error> {
            let chip = FiboChip::construct(config);
            let (mut a, mut b, mut c) =
                chip.load_private(layouter.namespace(|| "first row"), self.a, self.b, self.c)?;

            for _ in 3..self.num {
                let xor = chip.xor(layouter.namespace(|| "xor"), &b, &c)?;
                let new_c = chip.add(layouter.namespace(|| "add"), &a, &xor)?;
                a = b;
                b = c;
                c = new_c;
            }
            chip.load_table(layouter.namespace(|| "lookup table"))?;
            Ok(())
        }
    }

    pub fn get_sequence(a: u64, b: u64, c: u64, num: usize) -> Vec<u64> {
        let mut seq = vec![0; num];
        seq[0] = a;
        seq[1] = b;
        seq[2] = c;
        for i in 3..num {
            seq[i] = seq[i - 3] + (seq[i - 2] ^ seq[i - 1]);
        }
        seq
    }
}

pub(crate) mod merkle_tree {
    mod merkle_tree_gadget {
        pub const T: usize = 16;
        pub const RATE: usize = T - 1;

        pub use crate::{
            main_gate,
            poseidon::{PoseidonRO, ROPair},
        };

        pub type HasherChip<F> = <PoseidonRO<T, RATE> as ROPair<F>>::OnCircuit;
        pub type Spec<F> = crate::poseidon::Spec<F, T, RATE>;
        pub type MainGateConfig = main_gate::MainGateConfig<T>;

        pub mod chip {

            use itertools::Itertools;

            use super::{
                off_circuit::{self as merkle_tree, NodeUpdate, Sibling},
                HasherChip, MainGateConfig, Spec,
            };
            use crate::{
                halo2_proofs::{
                    circuit::AssignedCell,
                    halo2curves::ff::{FromUniformBytes, PrimeFieldBits},
                    plonk::Error as Halo2Error,
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
                                update.try_map(|f| {
                                    assigner.assign_next_advice(region, || "TODO", f)
                                })?,
                            ))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    region.next();

                    for ((index, update), (_next_index, next_update)) in
                        assigned_proof.iter().tuple_windows()
                    {
                        let (old_next, new_next) = match index
                            .get_sibling()
                            .map(|_| update.sibling.as_ref().expect("root unreachable"))
                        {
                            Sibling::Left(left) => {
                                let old_next = self
                                    .hasher_chip(&config)
                                    .update(
                                        &[left, &update.old]
                                            .map(|c| WrapValue::Assigned(c.clone())),
                                    )
                                    .squeeze(region)?;
                                let new_next = self
                                    .hasher_chip(&config)
                                    .update(
                                        &[left, &update.new]
                                            .map(|c| WrapValue::Assigned(c.clone())),
                                    )
                                    .squeeze(region)?;

                                (old_next, new_next)
                            }
                            Sibling::Right(right) => {
                                let old_next = self
                                    .hasher_chip(&config)
                                    .update(
                                        &[&update.old, right]
                                            .map(|c| WrapValue::Assigned(c.clone())),
                                    )
                                    .squeeze(region)?;
                                let new_next = self
                                    .hasher_chip(&config)
                                    .update(
                                        &[&update.new, right]
                                            .map(|c| WrapValue::Assigned(c.clone())),
                                    )
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
        }

        pub mod off_circuit {

            use std::{array, collections::HashMap, fmt, iter, num::NonZeroUsize};

            use itertools::Itertools;
            use serde::Serialize;
            use tracing::*;

            use super::{RATE, T};
            use crate::{
                halo2curves::ff::{FromUniformBytes, PrimeField, PrimeFieldBits},
                poseidon::{PoseidonRO, ROPair, Spec},
            };

            type Hasher<F> = <PoseidonRO<T, RATE> as ROPair<F>>::OffCircuit;

            pub const NUM_BITS: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(255) };
            const R_F: usize = 10;
            const R_P: usize = 10;

            pub fn hash<F>(l: F, r: F) -> F
            where
                F: Serialize + PrimeField + FromUniformBytes<64> + PrimeFieldBits,
            {
                Hasher::digest::<F>(Spec::new(R_F, R_P), &[l, r], NUM_BITS)
            }

            const DEPTH: u8 = 32;
            const DEPTH_SIZE: usize = DEPTH as usize;

            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct Level(u8);

            impl fmt::Display for Level {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "{}", self.0)
                }
            }

            impl Level {
                pub fn new(level: u8) -> Option<Self> {
                    level.lt(&DEPTH).then_some(Self(level))
                }
                pub const fn zero() -> Self {
                    Level(0)
                }
                pub const fn root() -> Self {
                    Level(DEPTH - 1)
                }
                pub const fn is_root(&self) -> bool {
                    self.0 == DEPTH - 1
                }
                pub fn get(&self) -> usize {
                    self.0 as usize
                }
                pub fn checked_next(&self) -> Option<Self> {
                    Self::new(self.0 + 1)
                }
                pub fn saturating_prev(&self) -> Self {
                    Self::new(self.0.saturating_sub(1)).unwrap()
                }
                pub fn iter_all() -> impl Iterator<Item = Self> {
                    iter::successors(Some(Level::zero()), Level::checked_next)
                }
            }

            #[derive(Debug, PartialEq, Eq, Hash, Clone)]
            pub struct Index {
                pub(crate) level: Level,
                pub(crate) index: u32,
            }

            impl Index {
                pub fn new(index: u32, level: Level) -> Option<Self> {
                    const LIMIT: u32 = 1 << 31;

                    index.lt(&LIMIT).then_some(Self { index, level })
                }
                pub fn root() -> Self {
                    Self {
                        level: Level::root(),
                        index: 0,
                    }
                }
            }

            impl fmt::Display for Index {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "[{}][{}]", self.level, self.index)
                }
            }

            #[derive(Debug, Clone)]
            pub enum Sibling<V> {
                Left(V),
                Right(V),
            }

            impl<V> Sibling<V> {
                pub fn map<T>(self, f: impl FnOnce(V) -> T) -> Sibling<T> {
                    match self {
                        Sibling::Left(l) => Sibling::Left(f(l)),
                        Sibling::Right(r) => Sibling::Right(f(r)),
                    }
                }
                pub fn unwrap(self) -> V {
                    match self {
                        Sibling::Left(l) => l,
                        Sibling::Right(r) => r,
                    }
                }
            }

            impl Index {
                pub fn is_root(&self) -> bool {
                    matches!(
                        &self,
                        Index {
                            index: 0,
                            level
                        } if level.is_root(),
                    )
                }

                pub fn next_level(&self) -> Option<Self> {
                    Some(Self {
                        level: self.level.checked_next()?,
                        index: self.index / 2,
                    })
                }
                pub fn get_sibling(&self) -> Sibling<Self> {
                    let level = self.level.clone();

                    if self.index % 2 == 0 {
                        Sibling::Right(Self {
                            level,
                            index: self.index + 1,
                        })
                    } else {
                        Sibling::Left(Self {
                            level,
                            index: self.index - 1,
                        })
                    }
                }
            }

            #[derive(Clone, Debug)]
            pub struct Tree<F: PrimeField> {
                filled_nodes: HashMap<Index, F>,
                default_values: [F; DEPTH_SIZE],
            }

            #[derive(Debug, Clone)]
            pub struct NodeUpdate<F> {
                /// Index of node in a level
                pub index: u32,
                /// Old value, before update
                pub old: F,
                /// New value, after update
                pub new: F,
                /// Sibling of this node, to calculate the next level value
                /// None for root
                pub sibling: Option<F>,
            }

            impl<F> NodeUpdate<F> {
                pub fn map<T>(self, mut f: impl FnMut(F) -> T) -> NodeUpdate<T> {
                    NodeUpdate {
                        index: self.index,
                        old: f(self.old),
                        new: f(self.new),
                        sibling: self.sibling.map(f),
                    }
                }

                pub fn try_map<T, E>(
                    self,
                    mut f: impl FnMut(F) -> Result<T, E>,
                ) -> Result<NodeUpdate<T>, E> {
                    Ok(NodeUpdate {
                        index: self.index,
                        old: f(self.old)?,
                        new: f(self.new)?,
                        sibling: self.sibling.map(f).transpose()?,
                    })
                }
            }

            #[derive(Debug, Clone)]
            pub struct Proof<F> {
                path: [NodeUpdate<F>; DEPTH_SIZE],
            }

            impl<F: PrimeField> Proof<F> {
                pub fn iter(&self) -> impl Iterator<Item = (Level, &NodeUpdate<F>)> {
                    Level::iter_all().zip(self.path.iter())
                }

                pub fn into_iter_with_level(self) -> impl Iterator<Item = (Level, NodeUpdate<F>)> {
                    Level::iter_all().zip(self.path)
                }

                pub fn root(&self) -> &NodeUpdate<F> {
                    self.path.last().unwrap()
                }
                pub fn start_root(&self) -> &NodeUpdate<F> {
                    self.path.first().unwrap()
                }
            }

            impl<F: PrimeField> Proof<F>
            where
                F: Serialize + PrimeField + FromUniformBytes<64> + PrimeFieldBits,
            {
                pub fn verify(&self) -> bool {
                    for (level, next_level) in Level::iter_all().tuple_windows() {
                        let NodeUpdate {
                            index,
                            old,
                            new,
                            sibling,
                        } = self.path[level.get()];

                        let index = Index { index, level };

                        debug!("start work with index: {index}");

                        let sibling = index
                            .get_sibling()
                            .map(|_| sibling.expect("root unreachable"));

                        let (old_next_value, new_next_value) = match &sibling {
                            Sibling::Left(left) => {
                                debug!("hash left {left:?} with {{ old:{old:?} , new:{new:?} }}");
                                (hash(*left, old), hash(*left, new))
                            }
                            Sibling::Right(right) => {
                                debug!("hash right {right:?} with {{ old:{old:?} , new:{new:?} }}");
                                (hash(old, *right), hash(new, *right))
                            }
                        };

                        let expected_old = self.path[next_level.get()].old;
                        if expected_old != old_next_value {
                            error!("`old` not match {expected_old:?} != {old_next_value:?}");
                            return false;
                        }

                        let expected_new = self.path[next_level.get()].new;
                        if expected_new != new_next_value {
                            error!("`new` not match {expected_new:?} != {new_next_value:?}");
                            return false;
                        }
                    }

                    true
                }
            }

            impl<F: PrimeField> Default for Tree<F>
            where
                F: Serialize + PrimeField + FromUniformBytes<64> + PrimeFieldBits,
            {
                fn default() -> Self {
                    let mut default_values = [hash(F::ZERO, F::ZERO); DEPTH_SIZE];

                    for (prev_lvl, lvl) in Level::iter_all().tuple_windows() {
                        let previous_level_value = default_values[prev_lvl.get()];
                        default_values[lvl.get()] =
                            hash(previous_level_value, previous_level_value);
                    }

                    Self {
                        default_values,
                        filled_nodes: HashMap::new(),
                    }
                }
            }

            impl<F: PrimeField> Tree<F>
            where
                F: Serialize + PrimeField + FromUniformBytes<64> + PrimeFieldBits,
            {
                pub fn get_root(&self) -> &F {
                    self.get_node(Index::root())
                }

                fn get_default_value(&self, level: &Level) -> &F {
                    self.default_values.get(level.get()).unwrap()
                }

                fn get_node(&self, index: Index) -> &F {
                    self.filled_nodes
                        .get(&index)
                        .unwrap_or_else(|| self.get_default_value(&index.level))
                }

                fn update_node(&mut self, index: Index, new_value: F) -> F {
                    self.filled_nodes
                        .insert(index.clone(), new_value)
                        .unwrap_or_else(|| *self.get_default_value(&index.level))
                }

                #[instrument(skip(self))]
                pub fn update_leaf(&mut self, index: u32, input: F) -> Proof<F> {
                    let mut current = Index::new(index, Level::zero()).unwrap();

                    let mut paths = array::from_fn(|_| None);
                    let new_leaf = hash(input, input);
                    let mut sibling = current.get_sibling().map(|s| *self.get_node(s));

                    paths[0] = Some(NodeUpdate {
                        index: current.index,
                        old: self.update_node(current.clone(), new_leaf),
                        new: new_leaf,
                        sibling: Some(sibling.clone().unwrap()),
                    });

                    loop {
                        debug!("Start with index: {current}");
                        let current_val = *self.get_node(current.clone());

                        let new_value = match &sibling {
                            Sibling::Left(left) => hash(*left, current_val),
                            Sibling::Right(right) => hash(current_val, *right),
                        };

                        current = current.next_level().unwrap_or_else(|| {
                            panic!("root will be found at prev cycle iteration: {:?}", current)
                        });

                        let old_value = self.update_node(current.clone(), new_value);
                        debug!(
                "hash{current}: sib:{sibling:?} with {current_val:?} is {new_value:?} from {old_value:?}"
            );

                        sibling = current.get_sibling().map(|s| *self.get_node(s));
                        paths[current.level.get()] = Some(NodeUpdate {
                            index: current.index,
                            old: old_value,
                            new: new_value,
                            sibling: Some(sibling.clone().unwrap()),
                        });

                        if current.is_root() {
                            break;
                        }
                    }

                    Proof {
                        path: paths.map(Option::unwrap),
                    }
                }
            }

            #[cfg(test)]
            mod test {
                use tracing_test::traced_test;

                use super::*;
                use crate::{halo2_proofs::arithmetic::Field, halo2curves::bn256::Fr};

                #[traced_test]
                #[test]
                fn simple_test() {
                    let mut tr = Tree::default();
                    debug!("{:?}", tr.default_values);
                    let mut rng = rand::thread_rng();
                    let pr1 = tr.update_leaf(3, Fr::random(&mut rng));
                    assert!(pr1.verify());

                    let pr2 = tr.update_leaf(3, Fr::random(&mut rng));
                    assert!(pr2.verify());

                    pr1.path
                        .iter()
                        .zip(pr2.path.iter())
                        .for_each(|(upd1, upd2)| {
                            assert_eq!(upd1.index, upd2.index);
                            assert_eq!(upd1.new, upd2.old);
                            assert_eq!(upd1.sibling, upd2.sibling);
                        });

                    let pr3 = tr.update_leaf((1u32 << 31) - 1, Fr::random(&mut rng));
                    assert!(pr3.verify());

                    pr3.path
                        .iter()
                        .zip(Level::iter_all())
                        .for_each(|(upd, level)| {
                            let default = *tr.get_default_value(&level);

                            // all nodes, but root, changed
                            if level != Level::root() {
                                assert_eq!(upd.old, default, "at {level} & {}", upd.index);
                            }

                            // sibling not filled only for root
                            if let Some(sibling) = upd.sibling {
                                // sibling for 31 level is not default
                                if level != Level::root().saturating_prev() {
                                    assert_eq!(sibling, default, "at {level}");
                                }
                            }
                        });
                }
            }
        }
    }

    use std::{collections::VecDeque, iter};

    use rand::Rng;
    use tracing::info;

    use crate::{
        halo2_proofs::{circuit::*, plonk::*},
        halo2curves::ff::{FromUniformBytes, PrimeFieldBits},
        ivc::{StepCircuit, SynthesisError},
        main_gate::{MainGate, RegionCtx},
    };

    const INDEX_LIMIT: u32 = 1 << 31;
    const ARITY: usize = 1;

    use merkle_tree_gadget::{
        chip::MerkleTreeUpdateChip,
        off_circuit::{NodeUpdate, Proof, Tree},
        *,
    };

    type ProofBatch<F> = Box<[Proof<F>]>;

    #[derive(Clone, Debug)]
    pub struct MerkleTreeUpdateCircuit<F>
    where
        F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
    {
        tree: Tree<F>,
        proofs_batches: VecDeque<ProofBatch<F>>,
        batch_size: usize,
    }

    impl<F> Default for MerkleTreeUpdateCircuit<F>
    where
        F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
    {
        fn default() -> Self {
            Self {
                tree: Default::default(),
                proofs_batches: VecDeque::new(),
                batch_size: 2,
            }
        }
    }

    impl<F> MerkleTreeUpdateCircuit<F>
    where
        F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
    {
        pub fn new(batch_size: usize) -> Self {
            Self {
                batch_size,
                ..Default::default()
            }
        }
        pub fn new_with_random_updates(
            rng: &mut impl Rng,
            batch_size: usize,
            batches_count: usize,
        ) -> Self {
            let mut self_ = Self::new(batch_size);

            for _ in 0..=batches_count {
                self_.random_update_leaves(rng);
            }

            self_
        }

        pub fn pop_front_proof_batch(&mut self) -> bool {
            self.proofs_batches.pop_front().is_some()
        }

        pub fn front_proof_batch(&self) -> &ProofBatch<F> {
            self.proofs_batches.front().as_ref().unwrap()
        }

        pub fn random_update_leaves(&mut self, mut rng: &mut impl Rng) {
            // 'allow' is necessary, because otherwise the closure captures rnd and we have to copy it
            #[allow(clippy::needless_borrows_for_generic_args)]
            self.update_leaves(iter::repeat_with(move || {
                (rng.gen::<u32>() % INDEX_LIMIT, F::random(&mut rng))
            }));
        }

        fn update_leaves(&mut self, update: impl Iterator<Item = (u32, F)>) -> (F, F) {
            assert!(update.size_hint().0 >= self.batch_size);
            let proofs = update
                .map(|(index, data)| self.tree.update_leaf(index, data))
                .take(self.batch_size)
                .collect::<Box<[_]>>();

            let old = proofs.first().unwrap().root().old;
            let new = proofs.last().unwrap().root().new;

            self.proofs_batches.push_back(proofs);

            (old, new)
        }
    }

    impl<F> StepCircuit<1, F> for MerkleTreeUpdateCircuit<F>
    where
        F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
    {
        type Config = MainGateConfig;
        fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
            MainGate::configure(cs)
        }

        fn process_step(
            &self,
            _z_i: &[F; ARITY],
            _k_table_size: u32,
        ) -> Result<[F; ARITY], SynthesisError> {
            Ok([self.front_proof_batch().last().as_ref().unwrap().root().new])
        }

        fn synthesize_step(
            &self,
            config: Self::Config,
            layouter: &mut impl Layouter<F>,
            z_i: &[AssignedCell<F, F>; 1],
        ) -> Result<[AssignedCell<F, F>; 1], SynthesisError> {
            layouter
                .assign_region(
                    || "",
                    |region| {
                        let mut region = RegionCtx::new(region, 0);

                        let mut prev = z_i[0].clone();
                        for proof in self.front_proof_batch().iter() {
                            let NodeUpdate { old, new, .. } =
                                MerkleTreeUpdateChip::new(proof.clone())
                                    .prove_next_update(&mut region, config.clone())?;

                            region.constrain_equal(prev.cell(), old.cell())?;
                            prev = new;
                        }
                        info!("offset = {}", region.offset);

                        Ok([prev])
                    },
                )
                .map_err(SynthesisError::Halo2)
        }
    }

    impl<F> Circuit<F> for MerkleTreeUpdateCircuit<F>
    where
        F: PrimeFieldBits + serde::Serialize + FromUniformBytes<64>,
    {
        type Config = <Self as StepCircuit<1, F>>::Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            todo!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            <Self as StepCircuit<1, F>>::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "",
                |region| {
                    let mut region = RegionCtx::new(region, 0);

                    region.next();

                    let mut prev = Option::<AssignedCell<F, F>>::None;
                    for proof in self.front_proof_batch().iter() {
                        let NodeUpdate { old, new, .. } = MerkleTreeUpdateChip::new(proof.clone())
                            .prove_next_update(&mut region, config.clone())?;

                        if let Some(prev) = prev {
                            region.constrain_equal(prev.cell(), old.cell())?;
                        }
                        prev = Some(new);
                    }

                    Ok([prev])
                },
            )?;

            Ok(())
        }
    }
}
