use crate::{btreeset::BTreeSet, Memory};
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::collections::BTreeSet as StdBTreeSet;
use test_strategy::proptest;

#[derive(Debug, Clone)]
enum Operation {
    Insert(Vec<u8>),
    Remove(Vec<u8>),
    Contains(Vec<u8>),
    Iter { from: usize, len: usize },
    Range { from: usize, len: usize },
    PopFirst,
    PopLast,
}

// A custom strategy that gives unequal weights to the different operations.
// Note that `Insert` has a higher weight than `Remove` so that, on average, BTreeSets
// are growing in size the more operations are executed.
fn operation_strategy() -> impl Strategy<Value = Operation> {
    prop_oneof![
        50 => any::<Vec<u8>>().prop_map(Operation::Insert),
        20 => any::<Vec<u8>>().prop_map(Operation::Remove),
        20 => any::<Vec<u8>>().prop_map(Operation::Contains),
        5 => (any::<usize>(), any::<usize>())
            .prop_map(|(from, len)| Operation::Iter { from, len }),
        5 => (any::<usize>(), any::<usize>())
            .prop_map(|(from, len)| Operation::Range { from, len }),
        2 => Just(Operation::PopFirst),
        2 => Just(Operation::PopLast),
    ]
}

// Runs a comprehensive test for the major stable BTreeSet operations.
// Results are validated against a standard BTreeSet.
#[proptest(cases = 10)]
fn comprehensive(#[strategy(pvec(operation_strategy(), 100..5_000))] ops: Vec<Operation>) {
    let mem = crate::btreeset::test::make_memory();
    let mut btreeset = BTreeSet::new(mem);
    let mut std_btreeset = StdBTreeSet::new();

    // Execute all the operations, validating that the stable btreeset behaves similarly to a std
    // btreeset.
    for op in ops.into_iter() {
        execute_operation(&mut std_btreeset, &mut btreeset, op);
    }
}

#[proptest]
fn set_min_max(#[strategy(pvec(any::<u64>(), 10..100))] keys: Vec<u64>) {
    crate::btreeset::test::run_btree_test(|mut set| {
        prop_assert_eq!(set.first(), None);
        prop_assert_eq!(set.last(), None);

        for (n, key) in keys.iter().enumerate() {
            set.insert(*key);

            let min = keys[0..=n].iter().min().unwrap();
            let max = keys[0..=n].iter().max().unwrap();

            prop_assert_eq!(set.first(), Some(*min));
            prop_assert_eq!(set.last(), Some(*max));
        }

        Ok(())
    });
}

// Given an operation, executes it on the given stable btreeset and standard btreeset, verifying
// that the result of the operation is equal in both btrees.
fn execute_operation<M: Memory>(
    std_btreeset: &mut StdBTreeSet<Vec<u8>>,
    btreeset: &mut BTreeSet<Vec<u8>, M>,
    op: Operation,
) {
    match op {
        Operation::Insert(key) => {
            let std_res = std_btreeset.insert(key.clone());

            eprintln!("Insert({})", hex::encode(&key));
            let res = btreeset.insert(key);
            assert_eq!(std_res, res);
        }
        Operation::Remove(key) => {
            let std_res = std_btreeset.remove(&key);

            eprintln!("Remove({})", hex::encode(&key));
            let res = btreeset.remove(&key);
            assert_eq!(std_res, res);
        }
        Operation::Contains(key) => {
            let std_res = std_btreeset.contains(&key);

            eprintln!("Contains({})", hex::encode(&key));
            let res = btreeset.contains(&key);
            assert_eq!(std_res, res);
        }
        Operation::Iter { from, len } => {
            assert_eq!(std_btreeset.len(), btreeset.len() as usize);
            if std_btreeset.is_empty() {
                return;
            }

            let from = from % std_btreeset.len();
            let len = len % std_btreeset.len();

            eprintln!("Iterate({}, {})", from, len);
            let std_iter = std_btreeset.iter().skip(from).take(len);
            let mut stable_iter = btreeset.iter().skip(from).take(len);
            for k1 in std_iter {
                let k2 = stable_iter.next().unwrap();
                assert_eq!(k1, &k2);
            }
            assert!(stable_iter.next().is_none());
        }
        Operation::Range { from, len } => {
            assert_eq!(std_btreeset.len(), btreeset.len() as usize);
            if std_btreeset.is_empty() {
                return;
            }

            eprintln!("Range({}, {})", from, len);
            let from = from % std_btreeset.len();
            let end = std::cmp::min(std_btreeset.len() - 1, from + len);

            // Create a range for the stable btreeset from the keys at indexes `from` and `end`.
            let range_start = btreeset.iter().skip(from).take(1).next().unwrap().clone();
            let range_end = btreeset.iter().skip(end).take(1).next().unwrap().clone();
            let stable_range = btreeset.range(range_start..range_end);

            // Create a range for the std btreeset from the keys at indexes `from` and `end`.
            let range_start = std_btreeset
                .iter()
                .skip(from)
                .take(1)
                .next()
                .unwrap()
                .clone();
            let range_end = std_btreeset
                .iter()
                .skip(end)
                .take(1)
                .next()
                .unwrap()
                .clone();
            let std_range = std_btreeset.range(range_start..range_end);

            for (k1, k2) in std_range.zip(stable_range) {
                assert_eq!(k1, &k2);
            }
        }
        Operation::PopFirst => {
            eprintln!("PopFirst");
            assert_eq!(std_btreeset.pop_first(), btreeset.pop_first());
        }
        Operation::PopLast => {
            eprintln!("PopLast");
            assert_eq!(std_btreeset.pop_last(), btreeset.pop_last());
        }
    };
}

#[proptest]
fn test_set_operations(
    #[strategy(pvec(any::<u64>(), 1..1000))] keys1: Vec<u64>,
    #[strategy(pvec(any::<u64>(), 1..1000))] keys2: Vec<u64>,
) {
    crate::btreeset::test::run_btree_test(|mut set1| {
        let mut set2 = BTreeSet::new(crate::btreeset::test::make_memory());
        let mut std_set1 = StdBTreeSet::new();
        let mut std_set2 = StdBTreeSet::new();

        for key in &keys1 {
            set1.insert(*key);
            std_set1.insert(*key);
        }

        for key in &keys2 {
            set2.insert(*key);
            std_set2.insert(*key);
        }

        let is_subset = set1.is_subset(&set2);
        let std_is_subset = std_set1.is_subset(&std_set2);
        prop_assert_eq!(is_subset, std_is_subset);

        let is_superset = set1.is_superset(&set2);
        let std_is_superset = std_set1.is_superset(&std_set2);
        prop_assert_eq!(is_superset, std_is_superset);

        let is_disjoint = set1.is_disjoint(&set2);
        let std_is_disjoint = std_set1.is_disjoint(&std_set2);
        prop_assert_eq!(is_disjoint, std_is_disjoint);

        let intersection: Vec<_> = set1.intersection(&set2).collect();
        let std_intersection: Vec<_> = std_set1.intersection(&std_set2).cloned().collect();
        prop_assert_eq!(intersection, std_intersection);

        let union: Vec<_> = set1.union(&set2).collect();
        let std_union: Vec<_> = std_set1.union(&std_set2).cloned().collect();
        prop_assert_eq!(union, std_union);

        let symmetric_diff: Vec<_> = set1.symmetric_difference(&set2).collect();
        let std_symmetric_diff: Vec<_> =
            std_set1.symmetric_difference(&std_set2).cloned().collect();
        prop_assert_eq!(symmetric_diff, std_symmetric_diff);

        Ok(())
    });
}
