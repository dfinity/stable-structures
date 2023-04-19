use super::*;
use proptest::array::uniform20;
use proptest::collection::vec as pvec;
use proptest::prelude::*;

proptest! {
    #[test]
    fn tuple_roundtrip(x in any::<u64>(), y in uniform20(any::<u8>())) {
        let tuple = (x, y);
        let bytes = tuple.to_bytes();
        prop_assert_eq!(bytes.len(), 28);
        prop_assert_eq!(tuple, Storable::from_bytes(bytes));
    }

    #[test]
    fn tuple_variable_width_u8_roundtrip(x in any::<u64>(), v in pvec(any::<u8>(), 0..40)) {
        let bytes = Blob::<48>::try_from(&v[..]).unwrap();
        let tuple = (x, bytes);
        prop_assert_eq!(tuple, Storable::from_bytes(tuple.to_bytes()));
    }

    #[test]
    fn tuple_variable_width_u16_roundtrip(x in any::<u64>(), v in pvec(any::<u8>(), 0..40)) {
        let bytes = Blob::<300>::try_from(&v[..]).unwrap();
        let tuple = (x, bytes);
        prop_assert_eq!(tuple, Storable::from_bytes(tuple.to_bytes()));
    }

    #[test]
    fn f64_roundtrip(v in any::<f64>()) {
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn f32_roundtrip(v in any::<f32>()) {
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn bool_roundtrip(v in any::<bool>()) {
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }
}

#[cfg(feature = "candid")]
#[test]
fn should_work_principal_roundtrip() {
    let v = Principal::from_text("aaaaa-aa").unwrap();
    assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    let v = Principal::from_text("2chl6-4hpzw-vqaaa-aaaaa-c").unwrap();
    assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    let v = Principal::anonymous();
    assert_eq!(v, Storable::from_bytes(v.to_bytes()));
}
