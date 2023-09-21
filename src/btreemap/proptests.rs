use crate::{
    btreemap::test::{b, btree_test},
    storable::Blob,
};
use proptest::collection::btree_set as pset;
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::collections::BTreeSet;
use test_strategy::proptest;

fn arb_blob() -> impl Strategy<Value = Blob<10>> {
    pvec(0..u8::MAX, 0..10).prop_map(|v| Blob::<10>::try_from(v.as_slice()).unwrap())
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
