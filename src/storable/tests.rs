use super::*;
use ic_principal::Principal;
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
    fn tuple_with_three_elements_fixed_size_roundtrip(x in any::<u64>(), y in uniform20(any::<u8>()), z in uniform20(any::<u8>())) {
        let tuple = (x, y, z);
        let bytes = tuple.to_bytes();
        // 8B x bytes | 20B y bytes | 20B z bytes
        prop_assert_eq!(bytes.len(), 48);
        prop_assert_eq!(tuple, Storable::from_bytes(bytes));
    }

    #[test]
    fn tuple_with_three_unbounded_elements_roundtrip(v1 in pvec(any::<u8>(), 0..4), v2 in pvec(any::<u8>(), 0..8), v3 in pvec(any::<u8>(), 0..12)) {
        let tuple = (v1, v2, v3);
        assert_eq!(tuple, Storable::from_bytes(tuple.to_bytes()));
    }

    #[test]
    fn tuple_with_three_elements_bounded_and_unbounded_roundtrip(x in pvec(any::<u8>(), 4..5), y in any::<u64>(), z in pvec(any::<u8>(), 12..13)) {
        let tuple = (x, y, z);
        let tuple_copy = tuple.clone();
        let bytes = tuple_copy.to_bytes();
        // 1B sizes len | 1B x size | 4B x bytes | 0B y size | 8B y bytes | 12B z bytes
        prop_assert_eq!(bytes.len(), 26);
        prop_assert_eq!(tuple, Storable::from_bytes(bytes));
    }


    #[test]
    fn tuple_variable_width_u8_roundtrip(x in any::<u64>(), v in pvec(any::<u8>(), 0..40)) {
        let bytes = Blob::<48>::try_from(&v[..]).unwrap();
        let tuple = (x, bytes);
        prop_assert_eq!(tuple, Storable::from_bytes(tuple.to_bytes()));
    }

    #[test]
    fn tuple_with_three_elements_variable_width_u8_roundtrip(x in any::<u64>(), v1 in pvec(any::<u8>(), 0..40), v2 in pvec(any::<u8>(), 0..80)) {
        let v1_bytes = Blob::<40>::try_from(&v1[..]).unwrap();
        let v2_bytes = Blob::<80>::try_from(&v2[..]).unwrap();
        let tuple = (x, v1_bytes, v2_bytes);
        prop_assert_eq!(tuple, Storable::from_bytes(tuple.to_bytes()));
    }

    #[test]
    fn tuple_variable_width_u16_roundtrip(x in any::<u64>(), v in pvec(any::<u8>(), 0..40)) {
        let bytes = Blob::<300>::try_from(&v[..]).unwrap();
        let tuple = (x, bytes);
        prop_assert_eq!(tuple, Storable::from_bytes(tuple.to_bytes()));
    }

    #[test]
    fn tuple_with_three_elements_variable_width_u16_roundtrip(x in any::<u64>(), v1 in pvec(any::<u8>(), 0..40), v2 in pvec(any::<u8>(), 0..80)) {
        let v1_bytes = Blob::<300>::try_from(&v1[..]).unwrap();
        let v2_bytes = Blob::<300>::try_from(&v2[..]).unwrap();

        let tuple = (x, v1_bytes, v2_bytes);
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
    fn optional_f64_roundtrip(v in proptest::option::of(any::<f64>())) {
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn optional_string_roundtrip(v in proptest::option::of(any::<String>())) {
        prop_assert_eq!(v.clone(), Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn optional_tuple_roundtrip(v in proptest::option::of((any::<u64>(), uniform20(any::<u8>())))) {
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn optional_tuple_with_three_elements_roundtrip(v in proptest::option::of((any::<u64>(), uniform20(any::<u8>()), uniform20(any::<u8>())))) {
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn optional_tuple_with_three_unbounded_elements_roundtrip(v in proptest::option::of((pvec(any::<u8>(), 0..4), pvec(any::<u8>(), 0..8),  pvec(any::<u8>(), 0..12)))) {
        prop_assert_eq!(v.clone(), Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn optional_tuple_variable_width_u8_roundtrip(v in proptest::option::of((any::<u64>(), pvec(any::<u8>(), 0..40)))) {
        let v = v.map(|(n, bytes)| (n, Blob::<48>::try_from(&bytes[..]).unwrap()));
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn optional_tuple_with_three_elements_variable_width_u8_roundtrip(v in proptest::option::of((any::<u64>(), pvec(any::<u8>(), 0..40), pvec(any::<u8>(), 0..80)))) {
        let v = v.map(|(n, bytes_1, bytes_2)| (n, Blob::<40>::try_from(&bytes_1[..]).unwrap(), Blob::<80>::try_from(&bytes_2[..]).unwrap()));
        prop_assert_eq!(v, Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn optional_tuple_with_three_elements_bounded_and_unbounded_roundtrip(v in proptest::option::of((any::<u64>(), pvec(any::<u8>(), 0..40), pvec(any::<u8>(), 0..80)))) {
        prop_assert_eq!(v.clone(), Storable::from_bytes(v.to_bytes()));
    }

    #[test]
    fn principal_roundtrip(mut bytes in pvec(any::<u8>(), 0..=28), tag in proptest::prop_oneof![Just(1),Just(2),Just(3),Just(4),Just(7)]) {
        bytes.push(tag);
        let principal = Principal::from_slice(bytes.as_slice());
        prop_assert_eq!(principal, Storable::from_bytes(principal.to_bytes()));
    }
}

#[test]
#[should_panic(expected = "expected an element with length <= 1 bytes, but found 4")]
fn to_bytes_checked_element_too_long_panics() {
    struct X;
    impl Storable for X {
        fn to_bytes(&self) -> Cow<[u8]> {
            Cow::Borrowed(&[1, 2, 3, 4])
        }

        fn from_bytes(_: Cow<[u8]>) -> Self {
            unimplemented!();
        }

        const BOUND: Bound = Bound::Bounded {
            max_size: 1,
            is_fixed_size: false,
        };
    }

    X.to_bytes_checked();
}

#[test]
fn to_bytes_checked_unbounded_element_no_panic() {
    struct X;
    impl Storable for X {
        fn to_bytes(&self) -> Cow<[u8]> {
            Cow::Borrowed(&[1, 2, 3, 4])
        }

        fn from_bytes(_: Cow<[u8]>) -> Self {
            unimplemented!();
        }

        const BOUND: Bound = Bound::Unbounded;
    }

    assert_eq!(X.to_bytes_checked(), Cow::Borrowed(&[1, 2, 3, 4]));
}

#[test]
fn to_bytes_checked_element_correct_size_no_panic() {
    struct X;
    impl Storable for X {
        fn to_bytes(&self) -> Cow<[u8]> {
            Cow::Borrowed(&[1, 2, 3, 4])
        }

        fn from_bytes(_: Cow<[u8]>) -> Self {
            unimplemented!();
        }

        const BOUND: Bound = Bound::Bounded {
            max_size: 4,
            is_fixed_size: false,
        };
    }

    assert_eq!(X.to_bytes_checked(), Cow::Borrowed(&[1, 2, 3, 4]));
}

#[test]
#[should_panic(expected = "expected a fixed-size element with length 5 bytes, but found 4")]
fn to_bytes_checked_fixed_element_wrong_size_panics() {
    struct X;
    impl Storable for X {
        fn to_bytes(&self) -> Cow<[u8]> {
            Cow::Borrowed(&[1, 2, 3, 4])
        }

        fn from_bytes(_: Cow<[u8]>) -> Self {
            unimplemented!();
        }

        const BOUND: Bound = Bound::Bounded {
            max_size: 5,
            is_fixed_size: true,
        };
    }

    X.to_bytes_checked();
}

#[test]
fn to_bytes_checked_fixed_element_correct_size_no_panic() {
    struct X;
    impl Storable for X {
        fn to_bytes(&self) -> Cow<[u8]> {
            Cow::Borrowed(&[1, 2, 3, 4, 5])
        }

        fn from_bytes(_: Cow<[u8]>) -> Self {
            unimplemented!();
        }

        const BOUND: Bound = Bound::Bounded {
            max_size: 5,
            is_fixed_size: true,
        };
    }

    assert_eq!(X.to_bytes_checked(), Cow::Borrowed(&[1, 2, 3, 4, 5]));
}

#[test]
fn storable_for_bool() {
    assert!(!bool::from_bytes(false.to_bytes()));
    assert!(bool::from_bytes(true.to_bytes()));
}

#[test]
fn tuple_with_three_elements_test_bound() {
    // <8B a_bytes> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(u64, u64, u64)>::BOUND.max_size(), 24);
    assert!(<(u64, u64, u64)>::BOUND.is_fixed_size());

    // <8B a_bytes> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(u64, u64, Blob<8>)>::BOUND.max_size(), 24);
    assert!(!<(u64, u64, Blob<8>)>::BOUND.is_fixed_size());

    // <1B size_lengths> <1B size_a> <8B a_bytes> <0B size_b> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(Blob<8>, u64, u64)>::BOUND.max_size(), 26);
    assert!(!<(Blob<8>, u64, u64)>::BOUND.is_fixed_size());

    // <1B size_lengths> <0B size_a> <8B a_bytes> <1B size_b> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(u64, Blob<8>, u64)>::BOUND.max_size(), 26);
    assert!(!<(u64, Blob<8>, u64)>::BOUND.is_fixed_size());

    // <1B size_lengths> <1B size_a> <8B a_bytes> <1B size_b> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(Blob<8>, Blob<8>, u64)>::BOUND.max_size(), 27);
    assert!(!<(Blob<8>, Blob<8>, u64)>::BOUND.is_fixed_size());

    // <1B size_lengths> <1B size_a> <8B a_bytes> <0B size_b> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(Blob<8>, u64, Blob<8>)>::BOUND.max_size(), 26);
    assert!(!<(Blob<8>, u64, Blob<8>)>::BOUND.is_fixed_size());

    // <1B size_lengths> <0B size_a> <8B a_bytes> <1B size_b> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(u64, Blob<8>, Blob<8>)>::BOUND.max_size(), 26);
    assert!(!<(u64, Blob<8>, Blob<8>)>::BOUND.is_fixed_size());

    // <1B size_lengths> <1B size_a> <8B a_bytes> <1B size_b> <8B b_bytes> <8B c_bytes>
    assert_eq!(<(Blob<8>, Blob<8>, Blob<8>)>::BOUND.max_size(), 27);
    assert!(!<(Blob<8>, Blob<8>, Blob<8>)>::BOUND.is_fixed_size());

    assert_eq!(<(Blob<8>, Blob<8>, String)>::BOUND, Bound::Unbounded);
    assert_eq!(<(Blob<8>, String, Blob<8>)>::BOUND, Bound::Unbounded);
    assert_eq!(<(String, Blob<8>, Blob<8>)>::BOUND, Bound::Unbounded);
    assert_eq!(<(String, String, Blob<8>)>::BOUND, Bound::Unbounded);
    assert_eq!(<(String, Blob<8>, String)>::BOUND, Bound::Unbounded);
    assert_eq!(<(Blob<8>, String, String)>::BOUND, Bound::Unbounded);
    assert_eq!(<(String, String, String)>::BOUND, Bound::Unbounded);
}
