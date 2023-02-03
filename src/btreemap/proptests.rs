use crate::StableBTreeMap;
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

proptest! {
    #[test]
    fn map_min_max(keys in pvec(any::<u64>(), 10..100)) {
        let mut map = StableBTreeMap::<u64, u64, _>::new(make_memory());

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
}
