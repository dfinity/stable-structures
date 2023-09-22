use crate::{
    btreemap::{
        test::{b, btree_test, make_memory},
        BTreeMap,
    },
    storable::Blob,
    Memory,
};
use proptest::collection::btree_set as pset;
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::collections::{BTreeMap as StdBTreeMap, BTreeSet};
use test_strategy::proptest;

#[derive(Debug, Clone)]
enum Operation {
    Insert { key: Vec<u8>, value: Vec<u8> },
    Iter { from: usize, len: usize },
    Get(usize),
    Remove(usize),
}

// A custom strategy that gives unequal weights to the different operations.
// Note that `Insert` has a higher weight than `Remove` so that, on average, BTreeMaps
// are growing in size the more operations are executed.
fn op_strategy() -> impl Strategy<Value = Operation> {
    prop_oneof![
        3 => (any::<Vec<u8>>(), any::<Vec<u8>>())
            .prop_map(|(key, value)| Operation::Insert { key, value }),
        1 => (any::<usize>(), any::<usize>())
            .prop_map(|(from, len)| Operation::Iter { from, len }),
        2 => (any::<usize>()).prop_map(Operation::Get),
        1 => (any::<usize>()).prop_map(Operation::Remove),
    ]
}

fn arb_blob() -> impl Strategy<Value = Blob<10>> {
    pvec(0..u8::MAX, 0..10).prop_map(|v| Blob::<10>::try_from(v.as_slice()).unwrap())
}

// Runs a comprehensive test for the major stable BTreeMap operations.
// Results are validated against a standard BTreeMap.
#[proptest(cases = 10)]
fn comprehensive(#[strategy(pvec(op_strategy(), 100..5_000))] ops: Vec<Operation>) {
    let mem = make_memory();
    let mut btree = BTreeMap::new(mem);
    let mut std_btree = StdBTreeMap::new();

    // Execute all the operations, validating that the stable btreemap behaves similarly to a std
    // btreemap.
    for op in ops.into_iter() {
        execute_operation(&mut std_btree, &mut btree, op);
    }
}

// A comprehensive fuzz test that runs until it's explicitly terminated. To run:
//
// ```
// cargo t comprehensive_fuzz -- --ignored --nocapture 2> comprehensive_fuzz.log
// ```
//
// comprehensive_fuzz.log contains all the operations to help triage a failure.
#[test]
#[ignore]
fn comprehensive_fuzz() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::default();

    let mem = make_memory();
    let mut btree = BTreeMap::new(mem);
    let mut std_btree = StdBTreeMap::new();

    let mut i = 0;

    loop {
        let op = op_strategy().new_tree(&mut runner).unwrap().current();
        execute_operation(&mut std_btree, &mut btree, op);
        i += 1;
        if i % 1000 == 0 {
            println!("=== Step {i} ===");
            println!("=== BTree Size: {}", btree.len());
        }
    }
}

#[proptest(cases = 10)]
fn insert(#[strategy(pset(arb_blob(), 1000..10_000))] keys: BTreeSet<Blob<10>>) {
    btree_test(|mut btree| {
        let keys = keys.clone();
        for key in keys.iter() {
            assert_eq!(btree.insert(*key, *key), None);
        }

        for key in keys.into_iter() {
            // Assert we retrieved the old value correctly.
            assert_eq!(btree.insert(key, b(&[])), Some(key));
            // Assert we retrieved the new value correctly.
            assert_eq!(btree.get(&key), Some(b(&[])));
        }
    });
}

#[proptest]
fn map_min_max(#[strategy(pvec(any::<u64>(), 10..100))] keys: Vec<u64>) {
    btree_test(|mut map| {
        prop_assert_eq!(map.first_key_value(), None);
        prop_assert_eq!(map.last_key_value(), None);

        for (n, key) in keys.iter().enumerate() {
            map.insert(*key, *key);

            let min = keys[0..=n].iter().min().unwrap();
            let max = keys[0..=n].iter().max().unwrap();

            prop_assert_eq!(map.first_key_value(), Some((*min, *min)));
            prop_assert_eq!(map.last_key_value(), Some((*max, *max)))
        }

        Ok(())
    });
}

#[proptest]
fn map_upper_bound_iter(#[strategy(pvec(0u64..u64::MAX -1 , 10..100))] keys: Vec<u64>) {
    btree_test(|mut map| {
        for k in keys.iter() {
            map.insert(*k, ());

            prop_assert_eq!(Some((*k, ())), map.iter_upper_bound(&(k + 1)).next());
        }

        Ok(())
    });
}

fn execute_operation<M: Memory>(
    std_btree: &mut StdBTreeMap<Vec<u8>, Vec<u8>>,
    btree: &mut BTreeMap<Vec<u8>, Vec<u8>, M>,
    op: Operation,
) {
    match op {
        Operation::Insert { key, value } => {
            let std_res = std_btree.insert(key.clone(), value.clone());

            eprintln!("Insert({}, {})", hex::encode(&key), hex::encode(&value));
            let res = btree.insert(key, value);
            assert_eq!(std_res, res);
        }
        Operation::Iter { from, len } => {
            assert_eq!(std_btree.len(), btree.len() as usize);
            if std_btree.is_empty() {
                return;
            }

            let from = from % std_btree.len();
            let len = len % std_btree.len();

            eprintln!("Iterate({}, {})", from, len);
            let std_iter = std_btree.iter().skip(from).take(len);
            let stable_iter = btree.iter().skip(from).take(len);
            for ((k1, v1), (k2, v2)) in std_iter.zip(stable_iter) {
                assert_eq!(k1, &k2);
                assert_eq!(v1, &v2);
            }
        }
        Operation::Get(idx) => {
            assert_eq!(std_btree.len(), btree.len() as usize);
            if std_btree.is_empty() {
                return;
            }
            let idx = idx % std_btree.len();

            if let Some((k, v)) = btree.iter().skip(idx).take(1).next() {
                eprintln!("Get({})", hex::encode(&k));
                assert_eq!(std_btree.get(&k), Some(&v));
                assert_eq!(btree.get(&k), Some(v));
            }
        }
        Operation::Remove(idx) => {
            assert_eq!(std_btree.len(), btree.len() as usize);
            if std_btree.is_empty() {
                return;
            }

            let idx = idx % std_btree.len();

            if let Some((k, v)) = btree.iter().skip(idx).take(1).next() {
                eprintln!("Remove({})", hex::encode(&k));
                assert_eq!(std_btree.remove(&k), Some(v.clone()));
                assert_eq!(btree.remove(&k), Some(v));
            }
        }
    };
}
