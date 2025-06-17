use crate::api_conformance::make_memory;
use crate::min_heap::MinHeap;
use std::cmp::Reverse;
use std::collections::BinaryHeap;

#[test]
fn api_conformance() {
    let mem = make_memory();
    let mut stable = MinHeap::new(mem).unwrap();
    let mut std = BinaryHeap::new();
    let n = 10_u32;

    // Push elements.
    for i in 0..n {
        stable.push(&i).expect("push failed");
        std.push(Reverse(i));
    }

    // Length and is_empty.
    // Note: stable.len() returns u64, std.len() returns usize.
    assert_eq!(stable.len(), std.len() as u64);
    assert_eq!(stable.is_empty(), std.is_empty());

    // Peek (min element).
    // Note: stable.peek() returns Option<T>, std.peek() returns Option<&Reverse<T>>.
    assert_eq!(stable.peek(), std.peek().map(|r| r.0));

    // Pop all elements, should match in ascending order.
    let mut stable_popped = Vec::new();
    let mut std_popped = Vec::new();
    while let Some(v) = stable.pop() {
        stable_popped.push(v);
    }
    while let Some(Reverse(v)) = std.pop() {
        std_popped.push(v);
    }
    assert_eq!(stable_popped, std_popped);

    // After popping everything, both should be empty.
    assert_eq!(stable.len(), 0);
    assert!(stable.is_empty());
    assert!(std.is_empty());
}
