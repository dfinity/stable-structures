use super::*;
use proptest::array::uniform20;
use proptest::collection::vec as pvec;
use proptest::prelude::*;

proptest! {
    #[test]
    fn tuple_roundtrip(x in any::<u64>(), y in uniform20(any::<u8>())) {
        let tuple = (x, y);
        let bytes = tuple.to_bytes().to_vec();
        prop_assert_eq!(bytes.len(), 28);
        prop_assert_eq!(tuple, Storable::from_bytes(bytes));
    }

    #[test]
    fn tuple_variable_width_rountrip(x in any::<u64>(), v in pvec(any::<u8>(), 0..40)) {
        let bytes = Bytes::<48>::try_from(&v[..]).unwrap();
        let tuple = (x, bytes);
        prop_assert_eq!(tuple, Storable::from_bytes(tuple.to_bytes().to_vec()));
    }

}
