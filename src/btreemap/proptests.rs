use crate::{btreemap::test::b, storable::Blob, BTreeMap};
use proptest::collection::btree_set as pset;
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

fn arb_blob() -> impl Strategy<Value = Blob<10>> {
    pvec(0..u8::MAX, 0..10).prop_map(|v| Blob::<10>::try_from(v.as_slice()).unwrap())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
    fn insert(keys in pset(arb_blob(), 1000..10_000)) {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        for key in keys.iter() {
            assert_eq!(btree.insert(*key, *key), None);
        }

        for key in keys.into_iter() {
            // Assert we retrieved the old value correctly.
            assert_eq!(btree.insert(key, b(&[])), Some(key));
            // Assert we retrieved the new value correctly.
            assert_eq!(btree.get(&key), Some(b(&[])));
        }
    }

    #[test]
    fn map_min_max(keys in pvec(any::<u64>(), 10..100)) {
        let mut map = BTreeMap::<u64, u64, _>::new(make_memory());

        prop_assert_eq!(map.first_key_value(), None);
        prop_assert_eq!(map.last_key_value(), None);

        for (n, key) in keys.iter().enumerate() {
            map.insert(*key, *key);

            let min = keys[0..=n].iter().min().unwrap();
            let max = keys[0..=n].iter().max().unwrap();

            prop_assert_eq!(map.first_key_value(), Some((*min, *min)));
            prop_assert_eq!(map.last_key_value(), Some((*max, *max)))
        }
    }

    #[test]
    fn map_upper_bound_iter(keys in pvec(0u64..u64::MAX -1 , 10..100)) {
        let mut map = BTreeMap::<u64, (), _>::new(make_memory());

        for k in keys.iter() {
            map.insert(*k, ());

            prop_assert_eq!(Some((*k, ())), map.iter_upper_bound(&(k + 1)).next());
        }
    }
}
