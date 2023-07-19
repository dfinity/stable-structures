use super::{InitError, MinHeap as StableMinHeap};
use crate::vec_mem::VectorMemory as M;
use crate::{GrowFailed, Memory};
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fmt::Debug;

#[derive(Debug, PartialEq, Clone)]
enum Operation<T> {
    Push(T),
    Pop,
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
        let mut h = BinaryHeap::new();
        let mut sh = StableMinHeap::<u64, M>::new(M::default()).unwrap();

        for op in ops {
            match op {
                Operation::Push(x) => {
                    sh.push(&x).unwrap();
                    h.push(Reverse(x));
                }
                Operation::Pop => {
                    prop_assert_eq!(sh.pop(), h.pop().map(|Reverse(x)| x));
                }
            }
        }
    }

    #[test]
    fn pop_sorted(mut items in pvec(any::<u64>(), 0..50)) {
        let mut sh = StableMinHeap::<u64, M>::new(M::default()).unwrap();
        for x in &items {
            sh.push(x).unwrap();
        }
        items.sort();
        for x in items {
            prop_assert_eq!(Some(x), sh.pop());
        }
    }
}

#[test]
fn test_simple_case() {
    let mut h = StableMinHeap::<u64, M>::new(M::default()).unwrap();
    assert_eq!(h.pop(), None);
    h.push(&0).unwrap();
    h.push(&3).unwrap();
    h.push(&0).unwrap();
    h.push(&1).unwrap();
    assert_eq!(h.pop(), Some(0));
    assert_eq!(h.pop(), Some(0));
    assert_eq!(h.pop(), Some(1));
    assert_eq!(h.pop(), Some(3));
    assert_eq!(h.len(), 0);
    assert!(h.is_empty());
}

#[test]
fn test_init_type_compatibility() {
    let h = StableMinHeap::<u64, M>::new(M::default()).unwrap();

    assert_eq!(
        StableMinHeap::<u32, M>::init(h.into_memory()).unwrap_err(),
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
        StableMinHeap::<u64, EmptyMem>::new(EmptyMem).unwrap_err(),
        GrowFailed {
            current_size: 0,
            delta: 1
        }
    );

    assert_eq!(
        StableMinHeap::<u64, EmptyMem>::init(EmptyMem).unwrap_err(),
        InitError::OutOfMemory,
    );

    let mem = M::default();
    mem.grow(1);
    mem.write(0, b"SVC\x01\x08\x00\x00\x00\x00\x00\x00\x00\x01");
    assert_eq!(
        StableMinHeap::<u64, M>::init(mem).unwrap_err(),
        InitError::BadMagic {
            actual: *b"SVC",
            expected: *b"SMH"
        },
    );

    let mem = M::default();
    mem.grow(1);
    mem.write(0, b"SMH\x0f\x08\x00\x00\x00\x00\x00\x00\x00\x01");
    assert_eq!(
        StableMinHeap::<u64, M>::init(mem).unwrap_err(),
        InitError::IncompatibleVersion(15),
    );
}
