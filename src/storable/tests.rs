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
    fn optional_tuple_variable_width_u8_roundtrip(x in  proptest::option::of(any::<u64>()), v in pvec(any::<u8>(), 0..40)) {
        let bytes = Blob::<48>::try_from(&v[..]).unwrap();
        let opt_tuple= if x.is_some() { Some((x.unwrap(),bytes))} else { None };
        prop_assert_eq!(opt_tuple, Storable::from_bytes(opt_tuple.to_bytes()));
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
