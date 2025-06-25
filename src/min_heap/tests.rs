use super::MinHeap as StableMinHeap;
use crate::vec_mem::VectorMemory as M;
use crate::Memory;
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
        let mut sh = StableMinHeap::<u64, M>::new(M::default());

        for op in ops {
            match op {
                Operation::Push(x) => {
                    sh.push(&x);
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
        let mut sh = StableMinHeap::<u64, M>::new(M::default());
        for x in &items {
            sh.push(x);
        }
        items.sort();
        for x in items {
            prop_assert_eq!(Some(x), sh.pop());
        }
    }
}

#[test]
fn test_simple_case() {
    let mut h = StableMinHeap::<u64, M>::new(M::default());
    assert_eq!(h.pop(), None);
    h.push(&0);
    h.push(&3);
    h.push(&0);
    h.push(&1);
    assert_eq!(h.pop(), Some(0));
    assert_eq!(h.pop(), Some(0));
    assert_eq!(h.pop(), Some(1));
    assert_eq!(h.pop(), Some(3));
    assert_eq!(h.len(), 0);
    assert!(h.is_empty());
}

#[test]
#[should_panic(expected = "IncompatibleElementType")]
fn test_failure_incompatible_element_type() {
    let h = StableMinHeap::<u64, M>::new(M::default());
    StableMinHeap::<u32, M>::init(h.into_memory());
}

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

#[test]
#[should_panic(expected = "GrowFailed { current_size: 0, delta: 1 }")]
fn test_failure_new() {
    StableMinHeap::<u64, EmptyMem>::new(EmptyMem);
}

#[test]
#[should_panic(expected = "OutOfMemory")]
fn test_failure_init() {
    StableMinHeap::<u64, EmptyMem>::init(EmptyMem);
}

#[test]
#[should_panic(expected = "BadMagic { actual: [83, 86, 67], expected: [83, 77, 72] }")]
fn test_failure_bad_magic() {
    // BadMagic { actual: *b"SVC", expected: *b"SMH" }
    let mem = M::default();
    mem.grow(1);
    mem.write(0, b"SVC\x01\x08\x00\x00\x00\x00\x00\x00\x00\x01");
    StableMinHeap::<u64, M>::init(mem);
}

#[test]
#[should_panic(expected = "IncompatibleVersion(15)")]
fn test_failure_incompatible_version() {
    let mem = M::default();
    mem.grow(1);
    mem.write(0, b"SMH\x0f\x08\x00\x00\x00\x00\x00\x00\x00\x01");
    StableMinHeap::<u64, M>::init(mem);
}
