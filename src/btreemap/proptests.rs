use crate::{
    btreemap::test::{b, btree_test},
    storable::{Blob, Bound},
    Storable,
};
use candid::Principal;
use proptest::collection::btree_set as pset;
use proptest::collection::vec as pvec;
use proptest::prelude::*;

fn arb_blob() -> impl Strategy<Value = Blob<10>> {
    pvec(0..u8::MAX, 0..10).prop_map(|v| Blob::<10>::try_from(v.as_slice()).unwrap())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
    fn insert(keys in pset(arb_blob(), 1000..10_000)) {
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

    #[test]
    fn map_min_max(keys in pvec(any::<u64>(), 10..100)) {
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

    #[test]
    fn map_upper_bound_iter(keys in pvec(0u64..u64::MAX -1 , 10..100)) {
        btree_test(|mut map| {
            for k in keys.iter() {
                map.insert(*k, ());

                prop_assert_eq!(Some((*k, ())), map.iter_upper_bound(&(k + 1)).next());
            }

            Ok(())
        });
    }
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct StorablePrincipal(pub Principal);

impl Storable for StorablePrincipal {
    fn to_bytes(&self) -> std::borrow::Cow<[u8]> {
        self.0.as_ref().into()
    }

    fn from_bytes(bytes: std::borrow::Cow<[u8]>) -> Self {
        Self(Principal::from_slice(bytes.as_ref()))
    }
    const BOUND: Bound = Bound::Bounded {
        max_size: 29,
        is_fixed_size: true,
    };
}

#[test]
fn insert_stable_principal() {
    btree_test(|mut btree| {
        let key1 = StorablePrincipal(candid::Principal::management_canister());
        let key2 = StorablePrincipal::from_bytes(key1.to_bytes());

        assert_eq!(key1, key2);

        btree.insert(key1.clone(), ());

        assert_eq!(btree.len(), 1);
        assert!(btree.contains_key(&key1));
    });
}
