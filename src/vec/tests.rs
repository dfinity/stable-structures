use super::{InitError, Vec as StableVec};
use crate::storable::{Bound, Storable};
use crate::vec_mem::VectorMemory as M;
use crate::{GrowFailed, Memory};
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::borrow::Cow;
use std::fmt::Debug;

#[derive(Debug, Clone, PartialEq)]
struct UnfixedU64<const N: u32>(u64);

impl<const N: u32> Storable for UnfixedU64<N> {
    fn to_bytes(&self) -> std::borrow::Cow<'_, [u8]> {
        self.0.to_bytes()
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        assert!(bytes.len() == 8);
        Self(u64::from_bytes(bytes))
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: N,
        is_fixed_size: false,
    };
}

#[derive(Debug, PartialEq, Clone)]
enum Operation<T> {
    Push(T),
    Pop,
}

fn arb_unfixed<const N: u32>(
    s: impl Strategy<Value = u64>,
) -> impl Strategy<Value = UnfixedU64<N>> {
    s.prop_map(UnfixedU64)
}

fn arb_op<T: Clone + Debug>(s: impl Strategy<Value = T>) -> impl Strategy<Value = Operation<T>> {
    prop_oneof![
        3 => s.prop_map(Operation::Push),
        1 => Just(Operation::Pop),
    ]
}

proptest! {
    #[test]
    fn push_pop_model_u64(ops in pvec(arb_op(any::<u64>()), 40)) {
        check_push_pop_model(ops)?;
    }

    #[test]
    fn push_pop_model_unfixed_255(ops in pvec(arb_op(arb_unfixed::<255>(any::<u64>())), 40)) {
        check_push_pop_model(ops)?;
    }

   #[test]
   fn push_pop_model_unfixed_65000(ops in pvec(arb_op(arb_unfixed::<65000>(any::<u64>())), 10)) {
       check_push_pop_model(ops)?;
   }

   #[test]
   fn push_pop_model_unfixed_68000(ops in pvec(arb_op(arb_unfixed::<68000>(any::<u64>())), 10)) {
       check_push_pop_model(ops)?;
   }

    #[test]
    fn init_after_new(vals in pvec(any::<u64>(), 0..20)) {
        let sv = StableVec::<u64, M>::new(M::default()).unwrap();
        for v in vals {
            sv.push(&v).unwrap();
        }
        let vec = sv.to_vec();
        prop_assert_eq!(StableVec::<u64, M>::init(sv.into_memory()).unwrap().to_vec(), vec);
    }
}

fn check_push_pop_model<T: Storable + Debug + Clone + PartialEq>(
    ops: Vec<Operation<T>>,
) -> Result<(), TestCaseError> {
    let mut v = Vec::new();
    let sv = StableVec::<T, M>::new(M::default()).unwrap();

    for op in ops {
        match op {
            Operation::Push(x) => {
                sv.push(&x).unwrap();
                v.push(x);
                prop_assert_eq!(&sv.to_vec(), &v);
            }
            Operation::Pop => {
                prop_assert_eq!(sv.pop(), v.pop());
                prop_assert_eq!(&sv.to_vec(), &v);
            }
        }
    }
    Ok(())
}

#[test]
fn test_init_type_compatibility() {
    let v = StableVec::<u64, M>::new(M::default()).unwrap();

    assert_eq!(
        StableVec::<u32, M>::init(v.into_memory()).unwrap_err(),
        InitError::IncompatibleElementType
    );

    let v = StableVec::<u64, M>::new(M::default()).unwrap();
    assert_eq!(
        StableVec::<UnfixedU64<8>, M>::init(v.into_memory()).unwrap_err(),
        InitError::IncompatibleElementType
    );
}

#[test]
fn test_init_failures() {
    struct EmptyMem;
    impl Memory for EmptyMem {
        fn size(&self) -> u64 {
            0
        }
        fn grow(&self, _: u64) -> i64 {
            -1
        }
        fn read(&self, _: u64, _: &mut [u8]) {
            panic!("out of bounds")
        }
        fn write(&self, _: u64, _: &[u8]) {
            panic!("out of bounds")
        }
    }

    assert_eq!(
        StableVec::<u64, EmptyMem>::new(EmptyMem).unwrap_err(),
        GrowFailed {
            current_size: 0,
            delta: 1
        }
    );

    assert_eq!(
        StableVec::<u64, EmptyMem>::init(EmptyMem).unwrap_err(),
        InitError::OutOfMemory,
    );

    let mem = M::default();
    mem.grow(1);
    mem.write(0, b"SIC\x01\x08\x00\x00\x00\x00\x00\x00\x00\x01");
    assert_eq!(
        StableVec::<u64, M>::init(mem).unwrap_err(),
        InitError::BadMagic {
            actual: *b"SIC",
            expected: *b"SVC"
        },
    );

    let mem = M::default();
    mem.grow(1);
    mem.write(0, b"SVC\x0f\x08\x00\x00\x00\x00\x00\x00\x00\x01");
    assert_eq!(
        StableVec::<u64, M>::init(mem).unwrap_err(),
        InitError::IncompatibleVersion(15),
    );
}

#[allow(clippy::iter_nth_zero)]
#[test]
fn test_iter() {
    let sv = StableVec::<u64, M>::new(M::default()).unwrap();
    assert_eq!(sv.iter().next(), None);
    sv.push(&1).unwrap();
    sv.push(&2).unwrap();
    sv.push(&3).unwrap();

    let mut iter = sv.iter();
    assert_eq!(iter.size_hint(), (3, None));
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.size_hint(), (2, None));
    assert_eq!(iter.next(), Some(2));
    assert_eq!(iter.size_hint(), (1, None));
    assert_eq!(iter.next(), Some(3));
    assert_eq!(iter.size_hint(), (0, None));
    assert_eq!(iter.next(), None);

    let mut iter_back = sv.iter();
    assert_eq!(iter_back.size_hint(), (3, None));
    assert_eq!(iter_back.next_back(), Some(3));
    assert_eq!(iter_back.size_hint(), (2, None));
    assert_eq!(iter_back.next_back(), Some(2));
    assert_eq!(iter_back.size_hint(), (1, None));
    assert_eq!(iter_back.next_back(), Some(1));
    assert_eq!(iter_back.size_hint(), (0, None));
    assert_eq!(iter_back.next_back(), None);

    let mut iter_mixed = sv.iter();
    assert_eq!(iter_mixed.size_hint(), (3, None));
    assert_eq!(iter_mixed.next_back(), Some(3));
    assert_eq!(iter_mixed.size_hint(), (2, None));
    assert_eq!(iter_mixed.next(), Some(1));
    assert_eq!(iter_mixed.size_hint(), (1, None));
    assert_eq!(iter_mixed.next_back(), Some(2));
    assert_eq!(iter_mixed.size_hint(), (0, None));
    assert_eq!(iter_mixed.next(), None);
    assert_eq!(iter_mixed.next_back(), None);

    assert_eq!(sv.iter().nth(0), Some(1));
    assert_eq!(sv.iter().nth(1), Some(2));
    assert_eq!(sv.iter().nth(2), Some(3));
    assert_eq!(sv.iter().nth(3), None);
    assert_eq!(sv.iter().nth(4), None);
    assert_eq!(sv.iter().nth(usize::MAX), None);

    assert_eq!(sv.iter().nth_back(0), Some(3));
    assert_eq!(sv.iter().nth_back(1), Some(2));
    assert_eq!(sv.iter().nth_back(2), Some(1));
    assert_eq!(sv.iter().nth_back(3), None);
    assert_eq!(sv.iter().nth_back(4), None);
    assert_eq!(sv.iter().nth_back(usize::MAX), None);

    assert_eq!(sv.iter().count(), 3);
    assert_eq!(sv.iter().count(), 3);
    assert_eq!(sv.iter().skip(1).count(), 2);
    assert_eq!(sv.iter().skip(2).count(), 1);
    assert_eq!(sv.iter().skip(3).count(), 0);
    assert_eq!(sv.iter().skip(4).count(), 0);
    assert_eq!(sv.iter().skip(usize::MAX).count(), 0);
}

#[test]
fn test_iter_count() {
    let sv = StableVec::<u64, M>::new(M::default()).unwrap();
    sv.push(&1).unwrap();
    sv.push(&2).unwrap();
    sv.push(&3).unwrap();
    sv.push(&4).unwrap();
    {
        let mut iter = sv.iter();
        iter.next_back();
        assert_eq!(iter.count(), 3);
    }
    {
        let mut iter = sv.iter();
        iter.next_back();
        sv.pop(); // this pops the element that we iterated through on the previous line
        sv.pop();
        assert_eq!(iter.count(), 2);
    }
}

// A struct with a bugg implementation of storable where the max_size can
// smaller than the serialized size.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
struct BuggyStruct(Vec<u8>);
impl crate::Storable for BuggyStruct {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(&self.0)
    }

    fn from_bytes(_: Cow<[u8]>) -> Self {
        unimplemented!();
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 1,
        is_fixed_size: false,
    };
}

#[test]
#[should_panic(expected = "expected an element with length <= 1 bytes, but found 4")]
fn push_element_bigger_than_max_size_panics() {
    let sv = StableVec::<BuggyStruct, M>::new(M::default()).unwrap();
    // Insert a struct where the serialized size is > `MAX_SIZE`. Should panic.
    sv.push(&BuggyStruct(vec![1, 2, 3, 4])).unwrap();
}

#[test]
#[should_panic(expected = "expected an element with length <= 1 bytes, but found 5")]
fn set_element_bigger_than_max_size_panics() {
    let sv = StableVec::<BuggyStruct, M>::new(M::default()).unwrap();
    // Insert a struct where the serialized size is <= `MAX_SIZE`. This should succeed.
    sv.push(&BuggyStruct(vec![1])).unwrap();

    // Insert a struct where the serialized size is > `MAX_SIZE`. Should panic.
    sv.set(0, &BuggyStruct(vec![1, 2, 3, 4, 5]));
}

#[test]
fn set_last_element_to_large_blob() {
    use crate::storable::Blob;
    let sv = StableVec::<Blob<65536>, M>::new(M::default()).unwrap();

    // Store a small blob.
    sv.push(&Blob::default()).unwrap();

    // Store a large blob that would require growing the memory.
    sv.set(0, &Blob::try_from(vec![1; 65536].as_slice()).unwrap());
}
