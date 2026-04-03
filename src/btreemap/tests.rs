use super::*;
use crate::{
    btreemap::iter::LazyEntry,
    storable::{Blob, Bound as StorableBound},
    VectorMemory,
};
use std::cell::RefCell;
use std::convert::TryFrom;
use std::rc::Rc;

/// A helper function to clone and collect borrowed key/value pairs into a `Vec`.
fn collect_kv<'a, K: Clone + 'a, V: Clone + 'a>(
    iter: impl Iterator<Item = (&'a K, &'a V)>,
) -> Vec<(K, V)> {
    iter.map(|(k, v)| (k.clone(), v.clone())).collect()
}

/// A helper function to collect owned key/value pairs into a `Vec`.
fn collect<K: Clone, V: Clone>(it: impl Iterator<Item = (K, V)>) -> Vec<(K, V)> {
    it.collect()
}

/// A helper function to collect lazy entries into a `Vec`.
fn collect_entry<'a, K, V, M>(it: impl Iterator<Item = LazyEntry<'a, K, V, M>>) -> Vec<(K, V)>
where
    K: Storable + Ord + Clone + 'a,
    V: Storable + 'a,
    M: Memory + 'a,
{
    it.map(|entry| entry.into_pair()).collect()
}

/// Returns a fixed‑size buffer for the given u32.
fn monotonic_buffer<const N: usize>(i: u32) -> [u8; N] {
    let mut buf = [0u8; N];
    let bytes = i.to_be_bytes();
    buf[N - bytes.len()..].copy_from_slice(&bytes);
    buf
}

#[test]
fn test_monotonic_buffer() {
    let cases: &[(u32, [u8; 4])] = &[
        (1, [0, 0, 0, 1]),
        (2, [0, 0, 0, 2]),
        ((1 << 8) - 1, [0, 0, 0, 255]),
        ((1 << 8), [0, 0, 1, 0]),
        ((1 << 16) - 1, [0, 0, 255, 255]),
        (1 << 16, [0, 1, 0, 0]),
        ((1 << 24) - 1, [0, 255, 255, 255]),
        (1 << 24, [1, 0, 0, 0]),
    ];

    for &(input, expected) in cases {
        let output = monotonic_buffer::<4>(input);
        assert_eq!(
            output, expected,
            "monotonic_buffer::<4>({}) returned {:?}, expected {:?}",
            input, output, expected
        );
    }
}

/// A trait to construct a value from a u32.
trait Builder {
    fn build(i: u32) -> Self;
    fn empty() -> Self;
}

impl Builder for () {
    fn build(_i: u32) -> Self {}
    fn empty() -> Self {}
}

impl Builder for u32 {
    fn build(i: u32) -> Self {
        i
    }
    fn empty() -> Self {
        0
    }
}

impl<const N: usize> Builder for Blob<N> {
    fn build(i: u32) -> Self {
        Blob::try_from(&monotonic_buffer::<N>(i)[..]).unwrap()
    }
    fn empty() -> Self {
        Blob::try_from(&[][..]).unwrap()
    }
}

type MonotonicVec32 = Vec<u8>;
impl Builder for MonotonicVec32 {
    fn build(i: u32) -> Self {
        monotonic_buffer::<32>(i).to_vec()
    }
    fn empty() -> Self {
        Vec::new()
    }
}

type MonotonicString32 = String;
impl Builder for MonotonicString32 {
    fn build(i: u32) -> Self {
        format!("{i:0>32}")
    }
    fn empty() -> Self {
        String::new()
    }
}

/// Encodes an object into a byte vector.
fn encode<T: Storable>(object: T) -> Vec<u8> {
    object.into_bytes_checked()
}

/// A helper method to succinctly create a blob.
pub(crate) fn b(x: &[u8]) -> Blob<10> {
    Blob::<10>::try_from(x).unwrap()
}

/// Creates a new shared memory instance.
pub(crate) fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

/// A test runner that runs the test using V1, migrated V2, and direct V2.
pub fn run_btree_test<K, V, R, F>(f: F)
where
    K: Storable + Ord + Clone,
    V: Storable,
    F: Fn(BTreeMap<K, V, VectorMemory>) -> R,
{
    // V1 does not support unbounded types.
    if K::BOUND != StorableBound::Unbounded && V::BOUND != StorableBound::Unbounded {
        // Test with V1.
        let mem = make_memory();
        let tree_v1 = BTreeMap::new_v1(mem);
        f(tree_v1);

        // Test with V2 migrated from V1.
        let mem = make_memory();
        let tree_v1: BTreeMap<K, V, _> = BTreeMap::new_v1(mem);
        let tree_v2_migrated = BTreeMap::load_helper(tree_v1.into_memory(), true);
        f(tree_v2_migrated);
    }

    // Test with direct V2.
    let mem = make_memory();
    let tree_v2 = BTreeMap::new(mem);
    f(tree_v2);
}

/// Like `run_btree_test` but only tests V2 with a specific cache size.
/// Used for cache-variant tests where V1/migration coverage is not needed
/// (the original non-cached test already covers those).
pub fn run_btree_test_cached<K, V, R, F>(cache_slots: usize, f: F)
where
    K: Storable + Ord + Clone,
    V: Storable,
    F: Fn(BTreeMap<K, V, VectorMemory>) -> R,
{
    let mem = make_memory();
    let tree = BTreeMap::new(mem).with_node_cache(cache_slots);
    f(tree);
}

/// Checks that objects from boundary u32 values are strictly increasing.
/// This ensures multi-byte conversions preserve order.
fn verify_monotonic<T: Builder + PartialOrd>() {
    for shift_bits in [8, 16, 24] {
        let i = (1 << shift_bits) - 1;
        assert!(
            T::build(i) < T::build(i + 1),
            "Monotonicity failed at i: {i}",
        );
    }
}

/// Asserts that the associated `BOUND` for `$ty` is _not_ `Unbounded`.
macro_rules! assert_bounded {
    ($ty:ty) => {
        assert_ne!(<$ty>::BOUND, StorableBound::Unbounded, "Must be Bounded");
    };
}

/// Asserts that the associated `BOUND` for `$ty` _is_ `Unbounded`.
macro_rules! assert_unbounded {
    ($ty:ty) => {
        assert_eq!(<$ty>::BOUND, StorableBound::Unbounded, "Must be Unbounded");
    };
}

macro_rules! run_with_key {
    ($runner:ident, $K:ty) => {{
        verify_monotonic::<$K>();

        // Empty value.
        $runner::<$K, ()>();

        // Bounded values.
        assert_bounded!(u32);
        $runner::<$K, u32>();

        assert_bounded!(Blob<20>);
        $runner::<$K, Blob<20>>();

        // Unbounded values.
        assert_unbounded!(MonotonicVec32);
        $runner::<$K, MonotonicVec32>();

        assert_unbounded!(MonotonicString32);
        $runner::<$K, MonotonicString32>();
    }};
}

/// Macro to apply a test function to a predefined grid of key/value types.
macro_rules! btree_test {
    ($name:ident, $runner:ident) => {
        #[test]
        fn $name() {
            // Bounded keys.
            assert_bounded!(u32);
            run_with_key!($runner, u32);

            assert_bounded!(Blob<10>);
            run_with_key!($runner, Blob<10>);

            // Unbounded keys.
            assert_unbounded!(MonotonicVec32);
            run_with_key!($runner, MonotonicVec32);

            assert_unbounded!(MonotonicString32);
            run_with_key!($runner, MonotonicString32);
        }
    };
}

// Define a trait for keys that need the full set of bounds.
trait TestKey: Storable + Ord + Clone + Builder + std::fmt::Debug {}
impl<T> TestKey for T where T: Storable + Ord + Clone + Builder + std::fmt::Debug {}

// Define a trait for values that need the full set of bounds.
trait TestValue: Storable + Clone + Builder + std::fmt::Debug + PartialEq {}
impl<T> TestValue for T where T: Storable + Clone + Builder + std::fmt::Debug + PartialEq {}

fn insert_get_init_preserves_data<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }

        // Reload the BTreeMap and verify the entry.
        let btree = BTreeMap::<K, V, VectorMemory>::init(btree.into_memory());
        for i in 0..n {
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }
    });
}
btree_test!(
    test_insert_get_init_preserves_data,
    insert_get_init_preserves_data
);

fn insert_overwrites_previous_value<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.insert(key(i), value(i + 1)), Some(value(i)));
            assert_eq!(btree.get(&key(i)), Some(value(i + 1)));
        }
    });
}
btree_test!(
    test_insert_overwrites_previous_value,
    insert_overwrites_previous_value
);

fn insert_same_key_many<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 1_000;
        assert_eq!(btree.insert(key(1), value(2)), None);
        for i in 2..n {
            assert_eq!(btree.insert(key(1), value(i + 1)), Some(value(i)));
        }
        assert_eq!(btree.get(&key(1)), Some(value(n)));
    });
}
btree_test!(test_insert_same_key_many, insert_same_key_many);

fn insert_overwrite_median_key_in_full_child_node<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        for i in 1..=17 {
            assert_eq!(btree.insert(key(i), value(0)), None);
        }

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, (12), 13, 14, 15, 16, 17]

        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(
            root.entries(btree.memory()),
            vec![(key(6), encode(value(0)))]
        );
        assert_eq!(root.children_len(), 2);

        // The right child should now be full, with the median key being "12"
        let right_child = btree.load_node(root.child(1));
        assert!(right_child.is_full());
        let median_index = right_child.entries_len() / 2;
        let median_key = key(12);
        assert_eq!(right_child.key(median_index, btree.memory()), &median_key);

        // Overwrite the value of the median key.
        assert_eq!(btree.insert(median_key.clone(), value(123)), Some(value(0)));
        assert_eq!(btree.get(&median_key), Some(value(123)));

        // The child has not been split and is still full.
        let right_child = btree.load_node(root.child(1));
        assert_eq!(right_child.node_type(), NodeType::Leaf);
        assert!(right_child.is_full());
    });
}
btree_test!(
    test_insert_overwrite_median_key_in_full_child_node,
    insert_overwrite_median_key_in_full_child_node
);

fn insert_overwrite_key_in_full_root_node<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), value(0)), None);
        }

        // We now have a root that is full and looks like this:
        //
        // [1, 2, 3, 4, 5, (6), 7, 8, 9, 10, 11]
        let root = btree.load_node(btree.root_addr);
        assert!(root.is_full());

        // Overwrite an element in the root. It should NOT cause the node to be split.
        assert_eq!(btree.insert(key(6), value(456)), Some(value(0)));

        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Leaf);
        assert_eq!(btree.get(&key(6)), Some(value(456)));
        assert_eq!(root.entries_len(), 11);
    });
}
btree_test!(
    test_insert_overwrite_key_in_full_root_node,
    insert_overwrite_key_in_full_root_node
);

fn allocations_without_split<K: TestKey, V: TestValue>() {
    let key = K::build;
    run_btree_test(|mut btree| {
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);

        assert_eq!(btree.insert(key(1), V::empty()), None);
        assert_eq!(btree.allocator.num_allocated_chunks(), 1);

        assert_eq!(btree.remove(&key(1)), Some(V::empty()));
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);
    });
}
btree_test!(test_allocations_without_split, allocations_without_split);

fn allocations_with_split<K: TestKey, V: TestValue>() {
    let key = K::build;
    run_btree_test(|mut btree| {
        // Insert entries until the root node is full.
        let mut i = 0;
        loop {
            assert_eq!(btree.insert(key(i), V::empty()), None);
            let root = btree.load_node(btree.root_addr);
            if root.is_full() {
                break;
            }
            i += 1;
        }

        // Only need a single allocation to store up to `CAPACITY` elements.
        assert_eq!(btree.allocator.num_allocated_chunks(), 1);

        assert_eq!(btree.insert(key(255), V::empty()), None);

        // The node had to be split into three nodes.
        assert_eq!(btree.allocator.num_allocated_chunks(), 3);
    });
}
btree_test!(test_allocations_with_split, allocations_with_split);

fn insert_split_node<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }

        // Should now split a node.
        let root = btree.load_node(btree.root_addr);
        assert!(root.is_full());
        assert_eq!(btree.insert(key(12), value(12)), None);

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }
    });
}
btree_test!(test_insert_split_node, insert_split_node);

fn insert_split_multiple_nodes<K: TestKey, V: TestValue>() {
    let key = K::build;
    let e = |i: u32| (key(i), encode(V::empty()));
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), V::empty()), None);
        }
        // Should now split a node.
        assert_eq!(btree.insert(key(12), V::empty()), None);

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(6)]);
        assert_eq!(root.children_len(), 2);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(1), e(2), e(3), e(4), e(5)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(7), e(8), e(9), e(10), e(11), e(12)]
        );

        for i in 1..=12 {
            assert_eq!(btree.get(&key(i)), Some(V::empty()));
        }

        // Insert more to cause more splitting.
        assert_eq!(btree.insert(key(13), V::empty()), None);
        assert_eq!(btree.insert(key(14), V::empty()), None);
        assert_eq!(btree.insert(key(15), V::empty()), None);
        assert_eq!(btree.insert(key(16), V::empty()), None);
        assert_eq!(btree.insert(key(17), V::empty()), None);
        // Should cause another split
        assert_eq!(btree.insert(key(18), V::empty()), None);

        for i in 1..=18 {
            assert_eq!(btree.get(&key(i)), Some(V::empty()));
        }

        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(6), e(12)],);
        assert_eq!(root.children_len(), 3);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(1), e(2), e(3), e(4), e(5)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(7), e(8), e(9), e(10), e(11)]
        );

        let child_2 = btree.load_node(root.child(2));
        assert_eq!(child_2.node_type(), NodeType::Leaf);
        assert_eq!(
            child_2.entries(btree.memory()),
            vec![e(13), e(14), e(15), e(16), e(17), e(18)]
        );

        assert_eq!(btree.allocator.num_allocated_chunks(), 4);
    });
}
btree_test!(
    test_insert_split_multiple_nodes,
    insert_split_multiple_nodes
);

fn first_key_value<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree: BTreeMap<K, V, _>| {
        assert_eq!(btree.first_key_value(), None);

        let n = 1_000;
        for i in (0..n).rev() {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.first_key_value(), Some((key(i), value(i))));
        }

        for i in 0..n {
            assert_eq!(btree.remove(&key(i)), Some(value(i)));
            if !btree.is_empty() {
                assert_eq!(btree.first_key_value(), Some((key(i + 1), value(i + 1))));
            }
        }
        assert_eq!(btree.first_key_value(), None);
    });
}
btree_test!(test_first_key_value, first_key_value);

fn last_key_value<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree: BTreeMap<K, V, _>| {
        assert_eq!(btree.last_key_value(), None);

        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.last_key_value(), Some((key(i), value(i))));
        }

        for i in (0..n).rev() {
            assert_eq!(btree.remove(&key(i)), Some(value(i)));
            if !btree.is_empty() {
                assert_eq!(btree.last_key_value(), Some((key(i - 1), value(i - 1))));
            }
        }
        assert_eq!(btree.last_key_value(), None);
    });
}
btree_test!(test_last_key_value, last_key_value);

fn pop_first_single_entry<K: TestKey, V: TestValue>() {
    let key = K::build;
    run_btree_test(|mut btree| {
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);

        assert_eq!(btree.insert(key(1), V::empty()), None);
        assert!(!btree.is_empty());
        assert_eq!(btree.allocator.num_allocated_chunks(), 1);

        assert_eq!(btree.pop_first(), Some((key(1), V::empty())));
        assert!(btree.is_empty());
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);
    });
}
btree_test!(test_pop_first_single_entry, pop_first_single_entry);

fn pop_last_single_entry<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);

        assert_eq!(btree.insert(key(1), value(1)), None);
        assert!(!btree.is_empty());
        assert_eq!(btree.allocator.num_allocated_chunks(), 1);

        assert_eq!(btree.pop_last(), Some((key(1), value(1))));
        assert!(btree.is_empty());
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);
    });
}
btree_test!(test_pop_last_single_entry, pop_last_single_entry);

fn remove_case_2a_and_2c<K: TestKey, V: TestValue>() {
    let key = K::build;
    let e = |i: u32| (key(i), encode(V::empty()));
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), V::empty()), None);
        }
        // Should now split a node.
        assert_eq!(btree.insert(key(0), V::empty()), None);

        // The result should look like this:
        //                    [6]
        //                   /   \
        // [0, 1, 2, 3, 4, 5]     [7, 8, 9, 10, 11]

        for i in 0..=11 {
            assert_eq!(btree.get(&key(i)), Some(V::empty()));
        }

        // Remove node 6. Triggers case 2.a
        assert_eq!(btree.remove(&key(6)), Some(V::empty()));

        // The result should look like this:
        //                [5]
        //               /   \
        // [0, 1, 2, 3, 4]   [7, 8, 9, 10, 11]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(5)]);
        assert_eq!(root.children_len(), 2);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(0), e(1), e(2), e(3), e(4)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(7), e(8), e(9), e(10), e(11)]
        );

        // There are three allocated nodes.
        assert_eq!(btree.allocator.num_allocated_chunks(), 3);

        // Remove node 5. Triggers case 2c
        assert_eq!(btree.remove(&key(5)), Some(V::empty()));

        // Reload the btree to verify that we saved it correctly.
        let btree = BTreeMap::<K, V, _>::load(btree.into_memory());

        // The result should look like this:
        // [0, 1, 2, 3, 4, 7, 8, 9, 10, 11]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(
            root.entries(btree.memory()),
            vec![e(0), e(1), e(2), e(3), e(4), e(7), e(8), e(9), e(10), e(11)]
        );

        // There is only one node allocated.
        assert_eq!(btree.allocator.num_allocated_chunks(), 1);
    });
}
btree_test!(test_remove_case_2a_and_2c, remove_case_2a_and_2c);

fn remove_case_2b<K: TestKey, V: TestValue>() {
    let key = K::build;
    let e = |i: u32| (key(i), encode(V::empty()));
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), V::empty()), None);
        }
        // Should now split a node.
        assert_eq!(btree.insert(key(12), V::empty()), None);

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&key(i)), Some(V::empty()));
        }

        // Remove node 6. Triggers case 2.b
        assert_eq!(btree.remove(&key(6)), Some(V::empty()));

        // The result should look like this:
        //                [7]
        //               /   \
        // [1, 2, 3, 4, 5]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(7)]);
        assert_eq!(root.children_len(), 2);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(1), e(2), e(3), e(4), e(5)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(8), e(9), e(10), e(11), e(12)]
        );

        // Remove node 7. Triggers case 2.c
        assert_eq!(btree.remove(&key(7)), Some(V::empty()));
        // The result should look like this:
        //
        // [1, 2, 3, 4, 5, 8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Leaf);
        assert_eq!(
            root.entries(btree.memory()),
            collect([1, 2, 3, 4, 5, 8, 9, 10, 11, 12].into_iter().map(e))
        );

        assert_eq!(btree.allocator.num_allocated_chunks(), 1);
    });
}
btree_test!(test_remove_case_2b, remove_case_2b);

fn remove_case_3a_right<K: TestKey, V: TestValue>() {
    let key = K::build;
    let e = |i: u32| (key(i), encode(V::empty()));
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), V::empty()), None);
        }

        // Should now split a node.
        assert_eq!(btree.insert(key(12), V::empty()), None);

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        // Remove node 3. Triggers case 3.a
        assert_eq!(btree.remove(&key(3)), Some(V::empty()));

        // The result should look like this:
        //                [7]
        //               /   \
        // [1, 2, 4, 5, 6]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(7)]);
        assert_eq!(root.children_len(), 2);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(1), e(2), e(4), e(5), e(6)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(8), e(9), e(10), e(11), e(12)]
        );

        // There are three allocated nodes.
        assert_eq!(btree.allocator.num_allocated_chunks(), 3);
    });
}
btree_test!(test_remove_case_3a_right, remove_case_3a_right);

fn remove_case_3a_left<K: TestKey, V: TestValue>() {
    let key = K::build;
    let e = |i: u32| (key(i), encode(V::empty()));
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), V::empty()), None);
        }
        // Should now split a node.
        assert_eq!(btree.insert(key(0), V::empty()), None);

        // The result should look like this:
        //                   [6]
        //                  /   \
        // [0, 1, 2, 3, 4, 5]   [7, 8, 9, 10, 11]

        // Remove node 8. Triggers case 3.a left
        assert_eq!(btree.remove(&key(8)), Some(V::empty()));

        // The result should look like this:
        //                [5]
        //               /   \
        // [0, 1, 2, 3, 4]   [6, 7, 9, 10, 11]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(5)]);
        assert_eq!(root.children_len(), 2);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(0), e(1), e(2), e(3), e(4)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(6), e(7), e(9), e(10), e(11)]
        );

        // There are three allocated nodes.
        assert_eq!(btree.allocator.num_allocated_chunks(), 3);
    });
}
btree_test!(test_remove_case_3a_left, remove_case_3a_left);

fn remove_case_3b_merge_into_right<K: TestKey, V: TestValue>() {
    let key = K::build;
    let e = |i: u32| (key(i), encode(V::empty()));
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), V::empty()), None);
        }
        // Should now split a node.
        assert_eq!(btree.insert(key(12), V::empty()), None);

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&key(i)), Some(V::empty()));
        }

        // Remove node 6. Triggers case 2.b
        assert_eq!(btree.remove(&key(6)), Some(V::empty()));
        // The result should look like this:
        //                [7]
        //               /   \
        // [1, 2, 3, 4, 5]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(7)]);
        assert_eq!(root.children_len(), 2);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(1), e(2), e(3), e(4), e(5)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(8), e(9), e(10), e(11), e(12)]
        );

        // There are three allocated nodes.
        assert_eq!(btree.allocator.num_allocated_chunks(), 3);

        // Remove node 3. Triggers case 3.b
        assert_eq!(btree.remove(&key(3)), Some(V::empty()));

        // Reload the btree to verify that we saved it correctly.
        let btree = BTreeMap::<K, V, _>::load(btree.into_memory());

        // The result should look like this:
        //
        // [1, 2, 4, 5, 7, 8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Leaf);
        assert_eq!(
            root.entries(btree.memory()),
            collect([1, 2, 4, 5, 7, 8, 9, 10, 11, 12].into_iter().map(e))
        );

        // There is only one allocated node remaining.
        assert_eq!(btree.allocator.num_allocated_chunks(), 1);
    });
}
btree_test!(
    test_remove_case_3b_merge_into_right,
    remove_case_3b_merge_into_right
);

fn remove_case_3b_merge_into_left<K: TestKey, V: TestValue>() {
    let key = K::build;
    let e = |i: u32| (key(i), encode(V::empty()));
    run_btree_test(|mut btree| {
        for i in 1..=11 {
            assert_eq!(btree.insert(key(i), V::empty()), None);
        }

        // Should now split a node.
        assert_eq!(btree.insert(key(12), V::empty()), None);

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&key(i)), Some(V::empty()));
        }

        // Remove node 6. Triggers case 2.b
        assert_eq!(btree.remove(&key(6)), Some(V::empty()));

        // The result should look like this:
        //                [7]
        //               /   \
        // [1, 2, 3, 4, 5]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(root.entries(btree.memory()), vec![e(7)]);
        assert_eq!(root.children_len(), 2);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![e(1), e(2), e(3), e(4), e(5)]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![e(8), e(9), e(10), e(11), e(12)]
        );

        // There are three allocated nodes.
        assert_eq!(btree.allocator.num_allocated_chunks(), 3);

        // Remove node 10. Triggers case 3.b where we merge the right into the left.
        assert_eq!(btree.remove(&key(10)), Some(V::empty()));

        // Reload the btree to verify that we saved it correctly.
        let btree = BTreeMap::<K, V, _>::load(btree.into_memory());

        // The result should look like this:
        //
        // [1, 2, 3, 4, 5, 7, 8, 9, 11, 12], 10 is gone
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Leaf);
        assert_eq!(
            root.entries(btree.memory()),
            vec![e(1), e(2), e(3), e(4), e(5), e(7), e(8), e(9), e(11), e(12)]
        );

        // There is only one allocated node remaining.
        assert_eq!(btree.allocator.num_allocated_chunks(), 1);
    });
}
btree_test!(
    test_remove_case_3b_merge_into_left,
    remove_case_3b_merge_into_left
);

fn insert_remove_many<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 10_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }

        let mut btree = BTreeMap::<K, V, _>::load(btree.into_memory());
        for i in 0..n {
            assert_eq!(btree.remove(&key(i)), Some(value(i)));
            assert_eq!(btree.get(&key(i)), None);
        }

        // We've deallocated everything.
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);
    });
}
btree_test!(test_insert_remove_many, insert_remove_many);

fn pop_first_many<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 10_000;

        assert!(btree.is_empty());
        assert_eq!(btree.pop_first(), None);

        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }
        assert_eq!(btree.len(), n as u64);

        let mut btree = BTreeMap::<K, V, _>::load(btree.into_memory());
        for i in 0..n {
            assert_eq!(btree.pop_first(), Some((key(i), value(i))));
            assert_eq!(btree.get(&key(i)), None);
        }

        // We've deallocated everything.
        assert!(btree.is_empty());
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);
    });
}
btree_test!(test_pop_first_many, pop_first_many);

fn pop_last_many<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 10_000;

        assert!(btree.is_empty());
        assert_eq!(btree.pop_last(), None);

        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }
        assert_eq!(btree.len(), n as u64);

        let mut btree = BTreeMap::<K, V, _>::load(btree.into_memory());
        for i in (0..n).rev() {
            assert_eq!(btree.pop_last(), Some((key(i), value(i))));
            assert_eq!(btree.get(&key(i)), None);
        }

        // We've deallocated everything.
        assert!(btree.is_empty());
        assert_eq!(btree.allocator.num_allocated_chunks(), 0);
    });
}
btree_test!(test_pop_last_many, pop_last_many);

fn reloading<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }
        assert_eq!(btree.len(), n as u64);

        // Reload the BTreeMap and verify the entry.
        let mut btree = BTreeMap::<K, V, VectorMemory>::load(btree.into_memory());
        assert_eq!(btree.len(), n as u64);
        for i in 0..n {
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }

        // Remove all entries and verify the entry.
        for i in 0..n {
            assert_eq!(btree.remove(&key(i)), Some(value(i)));
        }
        assert_eq!(btree.len(), 0);

        // Reload the BTreeMap and verify the entry.
        let btree = BTreeMap::<K, V, VectorMemory>::load(btree.into_memory());
        assert_eq!(btree.len(), 0);
    });
}
btree_test!(test_reloading, reloading);

fn len<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }

        assert_eq!(btree.len(), n as u64);
        assert!(!btree.is_empty());

        for i in 0..n {
            assert_eq!(btree.remove(&key(i)), Some(value(i)));
        }

        assert_eq!(btree.len(), 0);
        assert!(btree.is_empty());
    });
}
btree_test!(test_len, len);

fn contains_key<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        let n = 1_000;
        for i in (0..n).step_by(2) {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }

        // Only even keys should be present.
        for i in 0..n {
            assert_eq!(btree.contains_key(&key(i)), i % 2 == 0);
        }
    });
}
btree_test!(test_contains_key, contains_key);

fn range_empty<K: TestKey, V: TestValue>() {
    let key = K::build;
    run_btree_test(|btree: BTreeMap<K, V, _>| {
        // Test prefixes that don't exist in the map.
        assert_eq!(collect_entry(btree.range(key(0)..)), vec![]);
        assert_eq!(collect_entry(btree.range(key(10)..)), vec![]);
        assert_eq!(collect_entry(btree.range(key(100)..)), vec![]);
    });
}
btree_test!(test_range_empty, range_empty);

// Tests the case where the prefix is larger than all the entries in a leaf node.
fn range_leaf_prefix_greater_than_all_entries<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        btree.insert(key(0), value(0));

        // Test a prefix that's larger than the value in the leaf node. Should be empty.
        assert_eq!(collect_entry(btree.range(key(1)..)), vec![]);
    });
}
btree_test!(
    test_range_leaf_prefix_greater_than_all_entries,
    range_leaf_prefix_greater_than_all_entries
);

// Tests the case where the prefix is larger than all the entries in an internal node.
fn range_internal_prefix_greater_than_all_entries<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        for i in 1..=12 {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }

        // The result should look like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        // Test a prefix that's larger than the key in the internal node.
        assert_eq!(
            collect_entry(btree.range(key(7)..key(8))),
            vec![(key(7), value(7))]
        );
    });
}
btree_test!(
    test_range_internal_prefix_greater_than_all_entries,
    range_internal_prefix_greater_than_all_entries
);

fn range_various_prefixes<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        btree.insert(key(1), value(100));
        btree.insert(key(2), value(200));
        btree.insert(key(3), value(300));
        btree.insert(key(4), value(400));
        btree.insert(key(11), value(500));
        btree.insert(key(12), value(600));
        btree.insert(key(13), value(700));
        btree.insert(key(14), value(800));
        btree.insert(key(21), value(900));
        btree.insert(key(22), value(1_000));
        btree.insert(key(23), value(1_100));
        btree.insert(key(24), value(1_200));

        // The result should look like this:
        //                 [12]
        //                /    \
        // [1, 2, 3, 4, 11]    [13, 14, 21, 22, 23, 24]

        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(
            root.entries(btree.memory()),
            vec![(key(12), encode(value(600)))]
        );
        assert_eq!(root.children_len(), 2);

        // Tests a prefix that's smaller than the key in the internal node.
        assert_eq!(
            collect_entry(btree.range(key(0)..key(11))),
            vec![
                (key(1), value(100)),
                (key(2), value(200)),
                (key(3), value(300)),
                (key(4), value(400)),
            ]
        );

        // Tests a prefix that crosses several nodes.
        assert_eq!(
            collect_entry(btree.range(key(10)..key(20))),
            vec![
                (key(11), value(500)),
                (key(12), value(600)),
                (key(13), value(700)),
                (key(14), value(800)),
            ]
        );

        // Tests a prefix that's larger than the key in the internal node.
        assert_eq!(
            collect_entry(btree.range(key(20)..key(30))),
            vec![
                (key(21), value(900)),
                (key(22), value(1_000)),
                (key(23), value(1_100)),
                (key(24), value(1_200)),
            ]
        );
    });
}
btree_test!(test_range_various_prefixes, range_various_prefixes);

fn range_various_prefixes_2<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        btree.insert(key(1), value(100));
        btree.insert(key(2), value(200));
        btree.insert(key(3), value(300));
        btree.insert(key(4), value(400));
        btree.insert(key(12), value(500));
        btree.insert(key(14), value(600));
        btree.insert(key(16), value(700));
        btree.insert(key(18), value(800));
        btree.insert(key(19), value(900));
        btree.insert(key(21), value(1000));
        btree.insert(key(22), value(1100));
        btree.insert(key(23), value(1200));
        btree.insert(key(24), value(1300));
        btree.insert(key(25), value(1400));
        btree.insert(key(26), value(1500));
        btree.insert(key(27), value(1600));
        btree.insert(key(28), value(1700));
        btree.insert(key(29), value(1800));

        // The result should look like this:
        //                 [14, 23]
        //                /    |   \
        // [1, 2, 3, 4, 12]    |   [24, 25, 26, 27, 28, 29]
        //                     |
        //           [16, 18, 19, 21, 22]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(
            root.entries(btree.memory()),
            vec![
                (key(14), encode(value(600))),
                (key(23), encode(value(1200)))
            ]
        );
        assert_eq!(root.children_len(), 3);
        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![
                (key(1), encode(value(100))),
                (key(2), encode(value(200))),
                (key(3), encode(value(300))),
                (key(4), encode(value(400))),
                (key(12), encode(value(500))),
            ]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![
                (key(16), encode(value(700))),
                (key(18), encode(value(800))),
                (key(19), encode(value(900))),
                (key(21), encode(value(1000))),
                (key(22), encode(value(1100))),
            ]
        );

        let child_2 = btree.load_node(root.child(2));
        assert_eq!(
            child_2.entries(btree.memory()),
            vec![
                (key(24), encode(value(1300))),
                (key(25), encode(value(1400))),
                (key(26), encode(value(1500))),
                (key(27), encode(value(1600))),
                (key(28), encode(value(1700))),
                (key(29), encode(value(1800))),
            ]
        );

        // Tests a prefix that doesn't exist, but is in the middle of the root node.
        assert_eq!(collect_entry(btree.range(key(15)..key(16))), vec![]);

        // Tests a prefix beginning in the middle of the tree and crossing several nodes.
        assert_eq!(
            collect_entry(btree.range(key(15)..=key(26))),
            vec![
                (key(16), value(700)),
                (key(18), value(800)),
                (key(19), value(900)),
                (key(21), value(1000)),
                (key(22), value(1100)),
                (key(23), value(1200)),
                (key(24), value(1300)),
                (key(25), value(1400)),
                (key(26), value(1500)),
            ]
        );

        // Tests a prefix that crosses several nodes.
        assert_eq!(
            collect_entry(btree.range(key(10)..key(20))),
            vec![
                (key(12), value(500)),
                (key(14), value(600)),
                (key(16), value(700)),
                (key(18), value(800)),
                (key(19), value(900)),
            ]
        );

        // Tests a prefix that starts from a leaf node, then iterates through the root and right
        // sibling.
        assert_eq!(
            collect_entry(btree.range(key(20)..key(30))),
            vec![
                (key(21), value(1000)),
                (key(22), value(1100)),
                (key(23), value(1200)),
                (key(24), value(1300)),
                (key(25), value(1400)),
                (key(26), value(1500)),
                (key(27), value(1600)),
                (key(28), value(1700)),
                (key(29), value(1800)),
            ]
        );
    });
}
btree_test!(test_range_various_prefixes_2, range_various_prefixes_2);

fn range_large<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        const TOTAL: u32 = 2_000;
        const MID: u32 = TOTAL / 2;

        for i in 0..TOTAL {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }

        // Check range [0, MID): should yield exactly the first MID entries.
        let keys: Vec<_> = btree.range(key(0)..key(MID)).collect();
        assert_eq!(keys.len(), MID as usize);
        for (i, entry) in keys.into_iter().enumerate() {
            let j = i as u32;
            assert_eq!(*entry.key(), key(j));
            assert_eq!(entry.value(), value(j));
        }

        // Check range [MID, TOTAL): should yield the remaining entries.
        let keys: Vec<_> = btree.range(key(MID)..).collect();
        assert_eq!(keys.len(), (TOTAL - MID) as usize);
        for (i, entry) in keys.into_iter().enumerate() {
            let j = MID + i as u32;
            assert_eq!(*entry.key(), key(j));
            assert_eq!(entry.value(), value(j));
        }
    });
}
btree_test!(test_range_large, range_large);

fn range_various_prefixes_with_offset<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        btree.insert(key(1), value(100));
        btree.insert(key(2), value(200));
        btree.insert(key(3), value(300));
        btree.insert(key(4), value(400));
        btree.insert(key(11), value(500));
        btree.insert(key(12), value(600));
        btree.insert(key(13), value(700));
        btree.insert(key(14), value(800));
        btree.insert(key(21), value(900));
        btree.insert(key(22), value(1000));
        btree.insert(key(23), value(1100));
        btree.insert(key(24), value(1200));

        // The result should look like this:
        //                 [12]
        //                /    \
        // [1, 2, 3, 4, 11]    [13, 14, 21, 22, 23, 24]

        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(
            root.entries(btree.memory()),
            vec![(key(12), encode(value(600)))]
        );
        assert_eq!(root.children_len(), 2);

        assert_eq!(
            collect_entry(btree.range(key(0)..key(10))),
            vec![
                (key(1), value(100)),
                (key(2), value(200)),
                (key(3), value(300)),
                (key(4), value(400)),
            ]
        );

        // Tests an offset that has a keys somewhere in the range of keys of an internal node.
        assert_eq!(
            collect_entry(btree.range(key(13)..key(20))),
            vec![(key(13), value(700)), (key(14), value(800))]
        );

        // Tests an offset that's larger than the key in the internal node.
        assert_eq!(collect_entry(btree.range(key(25)..)), vec![]);
    });
}
btree_test!(
    test_range_various_prefixes_with_offset,
    range_various_prefixes_with_offset
);

fn range_various_prefixes_with_offset_2<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        btree.insert(key(1), value(0));
        btree.insert(key(2), value(0));
        btree.insert(key(3), value(0));
        btree.insert(key(4), value(0));
        btree.insert(key(12), value(0));
        btree.insert(key(14), value(0));
        btree.insert(key(16), value(0));
        btree.insert(key(18), value(0));
        btree.insert(key(19), value(0));
        btree.insert(key(21), value(0));
        btree.insert(key(22), value(0));
        btree.insert(key(23), value(0));
        btree.insert(key(24), value(0));
        btree.insert(key(25), value(0));
        btree.insert(key(26), value(0));
        btree.insert(key(27), value(0));
        btree.insert(key(28), value(0));
        btree.insert(key(29), value(0));

        // The result should look like this:
        //                 [14, 23]
        //                /    |   \
        // [1, 2, 3, 4, 12]    |   [24, 25, 26, 27, 28, 29]
        //                     |
        //           [16, 18, 19, 21, 22]
        let root = btree.load_node(btree.root_addr);
        assert_eq!(root.node_type(), NodeType::Internal);
        assert_eq!(
            root.entries(btree.memory()),
            vec![(key(14), encode(value(0))), (key(23), encode(value(0)))]
        );
        assert_eq!(root.children_len(), 3);

        let child_0 = btree.load_node(root.child(0));
        assert_eq!(child_0.node_type(), NodeType::Leaf);
        assert_eq!(
            child_0.entries(btree.memory()),
            vec![
                (key(1), encode(value(0))),
                (key(2), encode(value(0))),
                (key(3), encode(value(0))),
                (key(4), encode(value(0))),
                (key(12), encode(value(0))),
            ]
        );

        let child_1 = btree.load_node(root.child(1));
        assert_eq!(child_1.node_type(), NodeType::Leaf);
        assert_eq!(
            child_1.entries(btree.memory()),
            vec![
                (key(16), encode(value(0))),
                (key(18), encode(value(0))),
                (key(19), encode(value(0))),
                (key(21), encode(value(0))),
                (key(22), encode(value(0))),
            ]
        );

        let child_2 = btree.load_node(root.child(2));
        assert_eq!(
            child_2.entries(btree.memory()),
            vec![
                (key(24), encode(value(0))),
                (key(25), encode(value(0))),
                (key(26), encode(value(0))),
                (key(27), encode(value(0))),
                (key(28), encode(value(0))),
                (key(29), encode(value(0))),
            ]
        );

        // Tests a offset that crosses several nodes.
        assert_eq!(
            collect_entry(btree.range(key(14)..key(20))),
            vec![
                (key(14), value(0)),
                (key(16), value(0)),
                (key(18), value(0)),
                (key(19), value(0)),
            ]
        );

        // Tests a offset that starts from a leaf node, then iterates through the root and right
        // sibling.
        assert_eq!(
            collect_entry(btree.range(key(22)..key(30))),
            vec![
                (key(22), value(0)),
                (key(23), value(0)),
                (key(24), value(0)),
                (key(25), value(0)),
                (key(26), value(0)),
                (key(27), value(0)),
                (key(28), value(0)),
                (key(29), value(0)),
            ]
        );
    });
}
btree_test!(
    test_range_various_prefixes_with_offset_2,
    range_various_prefixes_with_offset_2
);

#[test]
#[should_panic(expected = "max_key_size must be <= 4")]
fn v1_rejects_increases_in_max_key_size() {
    let mem = make_memory();
    let btree: BTreeMap<Blob<4>, Blob<3>, _> = BTreeMap::init_v1(mem);
    let _btree: BTreeMap<Blob<5>, Blob<3>, _> = BTreeMap::init_v1(btree.into_memory());
}

#[test]
fn v2_handles_increases_in_max_key_size_and_max_value_size() {
    let mem = make_memory();
    let mut btree: BTreeMap<Blob<4>, Blob<4>, _> = BTreeMap::init(mem);
    btree.insert(
        [1u8; 4].as_slice().try_into().unwrap(),
        [1u8; 4].as_slice().try_into().unwrap(),
    );

    // Reinitialize the BTree with larger keys and value sizes.
    let mut btree: BTreeMap<Blob<5>, Blob<5>, _> = BTreeMap::init(btree.into_memory());
    btree.insert(
        [2u8; 5].as_slice().try_into().unwrap(),
        [2u8; 5].as_slice().try_into().unwrap(),
    );

    // Still able to retrieve all the entries inserted.
    assert_eq!(
        btree.get(&([1u8; 4].as_slice().try_into().unwrap())),
        Some([1u8; 4].as_slice().try_into().unwrap())
    );

    assert_eq!(
        btree.get(&([2u8; 5].as_slice().try_into().unwrap())),
        Some([2u8; 5].as_slice().try_into().unwrap())
    );
}

#[test]
fn accepts_small_or_equal_key_sizes() {
    let mem = make_memory();
    let btree: BTreeMap<Blob<4>, Blob<3>, _> = BTreeMap::init(mem);
    // Smaller key size
    let btree: BTreeMap<Blob<3>, Blob<3>, _> = BTreeMap::init(btree.into_memory());
    // Equal key size
    let _btree: BTreeMap<Blob<4>, Blob<3>, _> = BTreeMap::init(btree.into_memory());
}

#[test]
#[should_panic(expected = "max_value_size must be <= 3")]
fn v1_rejects_larger_value_sizes() {
    let mem = make_memory();
    let btree: BTreeMap<Blob<4>, Blob<3>, _> = BTreeMap::init_v1(mem);
    let _btree: BTreeMap<Blob<4>, Blob<4>, _> = BTreeMap::init_v1(btree.into_memory());
}

#[test]
fn accepts_small_or_equal_value_sizes() {
    let mem = make_memory();
    let btree: BTreeMap<Blob<4>, Blob<3>, _> = BTreeMap::init(mem);
    // Smaller key size
    let btree: BTreeMap<Blob<4>, Blob<2>, _> = BTreeMap::init(btree.into_memory());
    // Equal key size
    let _btree: BTreeMap<Blob<4>, Blob<3>, _> = BTreeMap::init(btree.into_memory());
}

fn bruteforce_range_search<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut stable_map| {
        use std::collections::BTreeMap;
        const NKEYS: u32 = 60;
        let mut std_map = BTreeMap::new();

        for i in 0..NKEYS {
            std_map.insert(key(i), value(i));
            stable_map.insert(key(i), value(i));
        }

        assert_eq!(
            collect_kv(std_map.range(..)),
            collect_entry(stable_map.range(..))
        );

        for l in 0..=NKEYS {
            assert_eq!(
                collect_kv(std_map.range(key(l)..)),
                collect_entry(stable_map.range(key(l)..))
            );

            assert_eq!(
                collect_kv(std_map.range(..key(l))),
                collect_entry(stable_map.range(..key(l)))
            );

            assert_eq!(
                collect_kv(std_map.range(..=key(l))),
                collect_entry(stable_map.range(..=key(l)))
            );

            for r in l + 1..=NKEYS {
                for lbound in [Bound::Included(key(l)), Bound::Excluded(key(l))] {
                    for rbound in [Bound::Included(key(r)), Bound::Excluded(key(r))] {
                        let range = (lbound.clone(), rbound);
                        assert_eq!(
                            collect_kv(std_map.range(range.clone())),
                            collect_entry(stable_map.range(range.clone())),
                            "range: {range:?}"
                        );
                    }
                }
            }
        }
    });
}
btree_test!(test_bruteforce_range_search, bruteforce_range_search);

fn test_iter_from_prev_key<K: TestKey, V: TestValue>() {
    let (key, value) = (K::build, V::build);
    run_btree_test(|mut btree| {
        for j in 0..100 {
            btree.insert(key(j), value(j));
            for i in 0..=j {
                assert_eq!(
                    btree
                        .iter_from_prev_key(&key(i + 1))
                        .next()
                        .map(|entry| entry.into_pair()),
                    Some((key(i), value(i))),
                    "failed to get an upper bound for key({})",
                    i + 1
                );
            }
            assert_eq!(
                btree
                    .iter_from_prev_key(&key(0))
                    .next()
                    .map(|entry| entry.into_pair()),
                None,
                "key(0) must not have an upper bound"
            );
        }
    });
}
btree_test!(test_test_iter_from_prev_key, test_iter_from_prev_key);

// A buggy implementation of storable where the max_size is smaller than the serialized size.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
struct BuggyStruct;
impl crate::Storable for BuggyStruct {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(&[1, 2, 3, 4])
    }

    fn into_bytes(self) -> Vec<u8> {
        self.to_bytes().into_owned()
    }

    fn from_bytes(_: Cow<[u8]>) -> Self {
        unimplemented!();
    }

    const BOUND: StorableBound = StorableBound::Bounded {
        max_size: 1,
        is_fixed_size: false,
    };
}

#[test]
#[should_panic(expected = "expected an element with length <= 1 bytes, but found 4")]
fn v1_panics_if_key_is_bigger_than_max_size() {
    let mut btree = BTreeMap::init_v1(make_memory());
    btree.insert(BuggyStruct, ());
}

#[test]
#[should_panic(expected = "expected an element with length <= 1 bytes, but found 4")]
fn v2_panics_if_key_is_bigger_than_max_size() {
    let mut btree = BTreeMap::init(make_memory());
    btree.insert(BuggyStruct, ());
}

#[test]
#[should_panic(expected = "expected an element with length <= 1 bytes, but found 4")]
fn v1_panics_if_value_is_bigger_than_max_size() {
    let mut btree = BTreeMap::init(make_memory());
    btree.insert((), BuggyStruct);
}

#[test]
#[should_panic(expected = "expected an element with length <= 1 bytes, but found 4")]
fn v2_panics_if_value_is_bigger_than_max_size() {
    let mut btree = BTreeMap::init(make_memory());
    btree.insert((), BuggyStruct);
}

// To generate the memory dump file for the current version:
//   cargo test create_btreemap_dump_file -- --include-ignored
#[test]
#[ignore]
fn create_btreemap_dump_file() {
    let mem = make_memory();
    let mut btree = BTreeMap::init_v1(mem.clone());

    let key = b(&[1, 2, 3]);
    let value = b(&[4, 5, 6]);
    assert_eq!(btree.insert(key, value), None);
    assert_eq!(btree.get(&key), Some(value));

    use std::io::prelude::*;
    let mut file = std::fs::File::create(format!("dumps/btreemap_v{LAYOUT_VERSION}.dump")).unwrap();
    file.write_all(&mem.borrow()).unwrap();
}

#[test]
fn produces_layout_identical_to_layout_version_1_with_packed_headers() {
    let mem = make_memory();
    let mut btree = BTreeMap::init_v1(mem.clone());

    let key = b(&[1, 2, 3]);
    let value = b(&[4, 5, 6]);
    assert_eq!(btree.insert(key, value), None);
    assert_eq!(btree.get(&key), Some(value));

    let btreemap_v1 = include_bytes!("../../dumps/btreemap_v1_packed_headers.dump");
    assert_eq!(*mem.borrow(), btreemap_v1);
}

#[test]
fn read_write_header_is_identical_to_read_write_struct() {
    #[repr(C, packed)]
    struct BTreePackedHeader {
        magic: [u8; 3],
        version: u8,
        max_key_size: u32,
        max_value_size: u32,
        root_addr: Address,
        length: u64,
        _buffer: [u8; 24],
    }
    let packed_header = BTreePackedHeader {
        magic: *MAGIC,
        version: LAYOUT_VERSION,
        root_addr: Address::from(0xDEADBEEF),
        max_key_size: 0x12345678,
        max_value_size: 0x87654321,
        length: 0xA1B2D3C4,
        _buffer: [0; 24],
    };

    let packed_mem = make_memory();
    crate::write_struct(&packed_header, Address::from(0), &packed_mem);

    let v1_header = BTreeHeader {
        version: Version::V1(DerivedPageSize {
            max_key_size: 0x12345678,
            max_value_size: 0x87654321,
        }),
        root_addr: Address::from(0xDEADBEEF),
        length: 0xA1B2D3C4,
    };

    let v1_mem = make_memory();
    BTreeMap::<Vec<_>, Vec<_>, RefCell<Vec<_>>>::write_header(&v1_header, &v1_mem);

    assert_eq!(packed_mem, v1_mem);

    let packed_header: BTreePackedHeader = crate::read_struct(Address::from(0), &v1_mem);
    let v1_header = BTreeMap::<Vec<_>, Vec<_>, RefCell<Vec<_>>>::read_header(&v1_mem);
    assert!(packed_header.magic == *MAGIC);
    assert!(packed_header.version == LAYOUT_VERSION);
    match v1_header.version {
        Version::V1(DerivedPageSize {
            max_key_size,
            max_value_size,
        }) => {
            assert!(packed_header.max_key_size == max_key_size);
            assert!(packed_header.max_value_size == max_value_size);
        }
        _ => unreachable!("version must be v1"),
    };

    assert!(packed_header.root_addr == v1_header.root_addr);
    assert!(packed_header.length == v1_header.length);
}

#[test]
fn migrate_from_bounded_to_unbounded_and_back() {
    // A type that is bounded.
    #[derive(PartialOrd, Ord, Clone, Eq, PartialEq, Debug)]
    struct T;
    impl Storable for T {
        fn to_bytes(&self) -> Cow<'_, [u8]> {
            Cow::Borrowed(&[1, 2, 3])
        }

        fn into_bytes(self) -> Vec<u8> {
            self.to_bytes().into_owned()
        }

        fn from_bytes(bytes: Cow<[u8]>) -> Self {
            assert_eq!(bytes.to_vec(), vec![1, 2, 3]);
            T
        }

        const BOUND: StorableBound = StorableBound::Bounded {
            max_size: 3,
            is_fixed_size: true,
        };
    }

    // Same as the above type, but unbounded.
    #[derive(PartialOrd, Ord, Clone, Eq, PartialEq, Debug)]
    struct T2;
    impl Storable for T2 {
        fn to_bytes(&self) -> Cow<'_, [u8]> {
            Cow::Owned(vec![1, 2, 3])
        }

        fn into_bytes(self) -> Vec<u8> {
            self.to_bytes().into_owned()
        }

        fn from_bytes(bytes: Cow<[u8]>) -> Self {
            assert_eq!(bytes.to_vec(), vec![1, 2, 3]);
            T2
        }

        const BOUND: StorableBound = StorableBound::Unbounded;
    }

    // Create a v1 btreemap with the bounded type.
    let mem = make_memory();
    let mut btree: BTreeMap<T, T, _> = BTreeMap::new_v1(mem);
    btree.insert(T, T);

    // Migrate to v2 and the unbounded type.
    let btree: BTreeMap<T2, T2, _> = BTreeMap::init(btree.into_memory());
    btree.save_header();

    // Reload the BTree again and try to read the value.
    let btree: BTreeMap<T2, T2, _> = BTreeMap::init(btree.into_memory());
    assert_eq!(btree.get(&T2), Some(T2));

    // Reload the BTree again with bounded type.
    let btree: BTreeMap<T, T, _> = BTreeMap::init(btree.into_memory());
    assert_eq!(btree.get(&T), Some(T));
}

#[test]
fn test_clear_new_bounded_type() {
    let mem = make_memory();
    let mut btree: BTreeMap<Blob<4>, Blob<4>, _> = BTreeMap::new(mem.clone());

    btree.insert(
        [1u8; 4].as_slice().try_into().unwrap(),
        [1u8; 4].as_slice().try_into().unwrap(),
    );

    assert_ne!(btree.len(), 0);
    assert_ne!(btree.allocator.num_allocated_chunks(), 0);
    assert_ne!(btree.root_addr, NULL);

    btree.clear_new();

    let header_actual = BTreeMap::<Blob<4>, Blob<4>, _>::read_header(&mem);

    BTreeMap::<Blob<4>, Blob<4>, _>::new(mem.clone());

    let header_expected = BTreeMap::<Blob<4>, Blob<4>, _>::read_header(&mem);

    assert_eq!(header_actual, header_expected);
}

#[test]
fn test_clear_new_unbounded_type() {
    let mem = make_memory();
    let mut btree: BTreeMap<String, String, _> = BTreeMap::new(mem.clone());
    btree.insert("asd".into(), "bce".into());

    assert_ne!(btree.len(), 0);
    assert_ne!(btree.allocator.num_allocated_chunks(), 0);
    assert_ne!(btree.root_addr, NULL);

    btree.clear_new();

    let header_actual = BTreeMap::<String, String, _>::read_header(&mem);

    BTreeMap::<String, String, _>::new(mem.clone());

    let header_expected = BTreeMap::<String, String, _>::read_header(&mem);

    assert_eq!(header_actual, header_expected);
}

#[test]
fn deallocating_node_with_overflows() {
    let mem = make_memory();
    let mut btree: BTreeMap<Vec<u8>, Vec<u8>, _> = BTreeMap::new(mem.clone());

    // No allocated chunks yet.
    assert_eq!(btree.allocator.num_allocated_chunks(), 0);

    // Insert and remove an entry that's large and requires overflow pages.
    btree.insert(vec![0; 10_000], vec![]);

    // At least two chunks should be allocated.
    // One for the node itself and at least one overflow page.
    assert!(btree.allocator.num_allocated_chunks() >= 2);
    btree.remove(&vec![0; 10_000]);

    // All chunks have been deallocated.
    assert_eq!(btree.allocator.num_allocated_chunks(), 0);
}

#[test]
fn repeatedly_deallocating_nodes_with_overflows() {
    let mem = make_memory();
    let mut btree: BTreeMap<Vec<u8>, Vec<u8>, _> = BTreeMap::new(mem.clone());

    // No allocated chunks yet.
    assert_eq!(btree.allocator.num_allocated_chunks(), 0);

    for _ in 0..100 {
        for i in 0..100 {
            btree.insert(vec![i; 10_000], vec![]);
        }

        for i in 0..100 {
            btree.remove(&vec![i; 10_000]);
        }
    }

    // All chunks have been deallocated.
    assert_eq!(btree.allocator.num_allocated_chunks(), 0);
}

#[test]
fn deallocating_root_does_not_leak_memory() {
    let mem = make_memory();
    let mut btree: BTreeMap<Vec<u8>, _, _> = BTreeMap::new(mem.clone());

    for i in 1..=11 {
        // Large keys are stored so that each node overflows.
        assert_eq!(btree.insert(vec![i; 10_000], ()), None);
    }

    // Should now split a node.
    assert_eq!(btree.insert(vec![0; 10_000], ()), None);

    // The btree should look like this:
    //                    [6]
    //                   /   \
    // [0, 1, 2, 3, 4, 5]     [7, 8, 9, 10, 11]
    let root = btree.load_node(btree.root_addr);
    assert_eq!(root.node_type(), NodeType::Internal);
    assert_eq!(root.keys(btree.memory()), vec![&[6; 10_000]]);
    assert_eq!(root.children_len(), 2);

    // Remove the element in the root.
    btree.remove(&vec![6; 10_000]);

    // The btree should look like this:
    //                 [5]
    //                /   \
    // [0, 1, 2, 3, 4]     [7, 8, 9, 10, 11]
    let root = btree.load_node(btree.root_addr);
    assert_eq!(root.node_type(), NodeType::Internal);
    assert_eq!(root.keys(btree.memory()), vec![&[5; 10_000]]);
    assert_eq!(root.children_len(), 2);

    // Remove the element in the root. This triggers the case where the root
    // node is deallocated and the children are merged into a single node.
    btree.remove(&vec![5; 10_000]);

    // The btree should look like this:
    //      [0, 1, 2, 3, 4, 7, 8, 9, 10, 11]
    let root = btree.load_node(btree.root_addr);
    assert_eq!(root.node_type(), NodeType::Leaf);
    assert_eq!(
        root.keys(btree.memory()),
        vec![
            &[0; 10_000],
            &[1; 10_000],
            &[2; 10_000],
            &[3; 10_000],
            &[4; 10_000],
            &[7; 10_000],
            &[8; 10_000],
            &[9; 10_000],
            &[10; 10_000],
            &[11; 10_000],
        ]
    );

    // Delete everything else.
    for i in 0..=11 {
        btree.remove(&vec![i; 10_000]);
    }

    assert_eq!(btree.allocator.num_allocated_chunks(), 0);
}

// ---------------------------------------------------------------------------
// Cache correctness tests
// ---------------------------------------------------------------------------

/// Runs `f` against a V2 BTreeMap with the given cache size.
fn run_with_cache<K, V, R>(cache_slots: usize, f: impl Fn(BTreeMap<K, V, VectorMemory>) -> R)
where
    K: Storable + Ord + Clone,
    V: Storable,
{
    let mem = make_memory();
    let tree = BTreeMap::new(mem).with_node_cache(cache_slots);
    f(tree);
}

/// Runs `f` with several cache sizes (disabled, tiny, default, large).
/// Includes non-power-of-two sizes — users can pass any value to with_node_cache.
fn run_with_various_cache_sizes<K, V, R>(f: impl Fn(BTreeMap<K, V, VectorMemory>) -> R)
where
    K: Storable + Ord + Clone,
    V: Storable,
{
    for slots in [0, 1, 3, 7, 16, 50] {
        run_with_cache(slots, &f);
    }
}

/// The cache must be invisible to the API: the same deterministic operation
/// sequence must produce identical results regardless of cache size.
#[test]
fn cache_vs_no_cache_equivalence() {
    let n = 500u64;

    // Collect results from a fixed operation sequence.
    let run_ops = |cache_slots: usize| -> Vec<String> {
        let mem = make_memory();
        let mut btree: BTreeMap<u64, u64, _> = BTreeMap::new(mem).with_node_cache(cache_slots);
        let mut results = Vec::new();

        // Insert
        for i in 0..n {
            results.push(format!("insert({i})={:?}", btree.insert(i, i * 10)));
        }
        // Overwrite half
        for i in (0..n).step_by(2) {
            results.push(format!("overwrite({i})={:?}", btree.insert(i, i * 100)));
        }
        // Get all
        for i in 0..n {
            results.push(format!("get({i})={:?}", btree.get(&i)));
        }
        // Contains
        for i in 0..n + 10 {
            results.push(format!("contains({i})={}", btree.contains_key(&i)));
        }
        // Remove some
        for i in (0..n).step_by(3) {
            results.push(format!("remove({i})={:?}", btree.remove(&i)));
        }
        // Get remaining
        for i in 0..n {
            results.push(format!("get2({i})={:?}", btree.get(&i)));
        }
        // first/last
        results.push(format!("first={:?}", btree.first_key_value()));
        results.push(format!("last={:?}", btree.last_key_value()));
        // Pop
        results.push(format!("pop_first={:?}", btree.pop_first()));
        results.push(format!("pop_last={:?}", btree.pop_last()));
        // Iterate remaining
        let entries: Vec<_> = btree.iter().map(|e| e.into_pair()).collect();
        results.push(format!("len={}", entries.len()));
        results.push(format!("entries={entries:?}"));

        results
    };

    let baseline = run_ops(0);
    for slots in [1, 3, 7, 16, 50, 256] {
        assert_eq!(
            baseline,
            run_ops(slots),
            "Results diverged with cache_slots={slots}"
        );
    }
}

/// Insert N keys, then get each one. Verifies the cache does not serve stale data.
#[test]
fn cache_insert_then_get() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i * 10);
        }
        for i in 0..n {
            assert_eq!(btree.get(&i), Some(i * 10), "get({i}) after insert");
        }
    });
}

/// Overwrite then get: must return new value, not stale cached value.
/// This is the exact pattern that broke the save_and_cache_node attempt.
#[test]
fn cache_overwrite_then_get() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
        }
        // Overwrite every key with a new value.
        for i in 0..n {
            let old = btree.insert(i, i + 1000);
            assert_eq!(old, Some(i), "overwrite({i}) old value");
        }
        // Read back: must see the new value, not the old cached one.
        for i in 0..n {
            assert_eq!(btree.get(&i), Some(i + 1000), "get({i}) after overwrite");
        }
    });
}

/// Insert until splits occur, then get every key.
/// Verifies split invalidation is correct.
#[test]
fn cache_split_then_get_all() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        // 500 keys is enough to cause multiple levels of splits.
        let n = 500;
        for i in 0..n {
            btree.insert(i, i);
        }
        for i in 0..n {
            assert_eq!(btree.get(&i), Some(i), "get({i}) after splits");
        }
    });
}

/// Insert many, remove until merges occur, get every remaining key.
/// Verifies merge invalidation.
#[test]
fn cache_merge_then_get_remaining() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        let n = 500;
        for i in 0..n {
            btree.insert(i, i);
        }
        // Remove every other key to trigger merges/rotations.
        for i in (0..n).step_by(2) {
            assert_eq!(btree.remove(&i), Some(i));
        }
        // Remaining odd keys must all be present.
        for i in (1..n).step_by(2) {
            assert_eq!(btree.get(&i), Some(i), "get({i}) after merges");
        }
        // Removed keys must be gone.
        for i in (0..n).step_by(2) {
            assert_eq!(btree.get(&i), None, "get({i}) should be None");
        }
    });
}

/// Sequential inserts into the same leaf area, then get all.
/// Tests the hot-leaf cache path.
#[test]
fn cache_sequential_inserts_then_gets() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        let n = 300;
        for i in 0..n {
            btree.insert(i, i);
            // Immediately verify the just-inserted key.
            assert_eq!(btree.get(&i), Some(i), "get({i}) right after insert");
        }
    });
}

/// Interleave insert, get, and remove on overlapping keys with a small cache.
/// Maximum eviction pressure.
#[test]
fn cache_interleaved_insert_get_remove() {
    for cache_slots in [1, 2, 4] {
        run_with_cache(cache_slots, |mut btree: BTreeMap<u64, u64, _>| {
            let n = 300u64;
            // Phase 1: insert all
            for i in 0..n {
                btree.insert(i, i);
            }
            // Phase 2: interleave operations
            for i in 0..n {
                // Get existing
                if i % 3 != 0 {
                    assert_eq!(btree.get(&i), Some(i), "get({i}) interleaved");
                }
                // Remove some
                if i % 3 == 0 {
                    assert_eq!(btree.remove(&i), Some(i));
                }
                // Re-insert with new value
                if i % 5 == 0 {
                    btree.insert(i, i + 1000);
                }
            }
            // Phase 3: verify final state
            for i in 0..n {
                let expected = if i % 5 == 0 {
                    Some(i + 1000)
                } else if i % 3 == 0 {
                    None
                } else {
                    Some(i)
                };
                assert_eq!(btree.get(&i), expected, "final get({i})");
            }
        });
    }
}

/// pop_first/pop_last in a loop, verify each returned entry.
/// Tests cache interaction with the single-pass pop algorithms.
#[test]
fn cache_pop_correctness() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
        }

        // Pop from front
        for i in 0..n / 2 {
            assert_eq!(btree.pop_first(), Some((i, i)), "pop_first step {i}");
        }

        // Pop from back
        for i in (n / 2..n).rev() {
            assert_eq!(btree.pop_last(), Some((i, i)), "pop_last step {i}");
        }

        assert!(btree.is_empty());
    });
}

/// Call first_key_value/last_key_value between inserts and removes.
/// Reproduces the pattern from the test_first_key_value failure.
#[test]
fn cache_first_last_during_mutations() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;

        // Insert in reverse order, check first_key_value after each insert.
        for i in (0..n).rev() {
            btree.insert(i, i);
            assert_eq!(
                btree.first_key_value(),
                Some((i, i)),
                "first_key_value after insert({i})"
            );
            assert_eq!(
                btree.last_key_value(),
                Some((n - 1, n - 1)),
                "last_key_value after insert({i})"
            );
        }

        // Remove from front, check first_key_value updates.
        for i in 0..n - 1 {
            btree.remove(&i);
            assert_eq!(
                btree.first_key_value(),
                Some((i + 1, i + 1)),
                "first_key_value after remove({i})"
            );
        }
    });
}

// ---------------------------------------------------------------------------
// Forward-looking tests for save-and-cache-node optimization
//
// These tests pass today (with invalidate-on-save). They are designed to
// catch stale-cache-after-save bugs if save_and_cache_node is implemented.
// ---------------------------------------------------------------------------

/// Insert entries into a leaf, then verify ALL entries (including ones that
/// were not just inserted) are still readable. Tests that lazy ByRef entries
/// in a cached node survive a save cycle.
#[test]
fn cache_saved_leaf_other_entries_readable() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        // Insert enough keys to have multiple entries per leaf.
        let n = 100u64;
        for i in 0..n {
            btree.insert(i, i * 10);
        }
        // Now overwrite a single key.
        btree.insert(50, 999);
        // Read ALL keys, not just the overwritten one.
        // If the cached leaf has stale lazy values, a different entry will
        // return wrong data.
        for i in 0..n {
            let expected = if i == 50 { 999 } else { i * 10 };
            assert_eq!(btree.get(&i), Some(expected), "get({i})");
        }
    });
}

/// Overwrite values of different sizes in the same node.
/// Tests that layout changes (from value size differences) do not break
/// cached lazy offsets.
#[test]
fn cache_overwrite_varying_value_sizes() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, Vec<u8>, _>| {
        let n = 100u64;
        // Insert with small values.
        for i in 0..n {
            btree.insert(i, vec![i as u8; 5]);
        }
        // Overwrite some with larger values.
        for i in (0..n).step_by(3) {
            btree.insert(i, vec![i as u8; 50]);
        }
        // Overwrite some with smaller values.
        for i in (1..n).step_by(3) {
            btree.insert(i, vec![i as u8; 1]);
        }
        // Verify all entries.
        for i in 0..n {
            let expected_len = if i % 3 == 0 {
                50
            } else if i % 3 == 1 {
                1
            } else {
                5
            };
            let val = btree.get(&i).unwrap();
            assert_eq!(val.len(), expected_len, "get({i}) value length");
            assert!(val.iter().all(|&b| b == i as u8), "get({i}) value content");
        }
    });
}

/// Trigger rotations/rebalancing, then read sibling entries.
/// Tests that rebalancing + cache does not corrupt neighboring nodes.
#[test]
fn cache_rebalance_then_read_siblings() {
    run_with_various_cache_sizes(|mut btree: BTreeMap<u64, u64, _>| {
        let n = 500u64;
        for i in 0..n {
            btree.insert(i, i);
        }
        // Remove keys in a pattern that forces rotations and merges at
        // various tree levels: remove every 3rd key, then every 2nd of
        // what remains.
        for i in (0..n).step_by(3) {
            btree.remove(&i);
        }
        let remaining: Vec<u64> = (0..n).filter(|i| i % 3 != 0).collect();
        for &i in remaining.iter().step_by(2) {
            btree.remove(&i);
        }
        // Verify all remaining keys are correct.
        for i in 0..n {
            let removed_pass1 = i % 3 == 0;
            let removed_pass2 = !removed_pass1 && {
                let pos = (0..n).filter(|j| j % 3 != 0).position(|j| j == i);
                pos.is_some_and(|p| p % 2 == 0)
            };
            if removed_pass1 || removed_pass2 {
                assert_eq!(btree.get(&i), None, "get({i}) should be removed");
            } else {
                assert_eq!(btree.get(&i), Some(i), "get({i}) should survive");
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Cached variants of existing tests
//
// Re-run selected existing test functions with specific cache sizes.
// Uses u32 key/value only (not the full type grid) to keep runtime bounded —
// the non-cached originals already cover the full type matrix.
// ---------------------------------------------------------------------------

#[test]
fn cached_insert_get_cache_1() {
    let (key, value) = (u32::build, u32::build);
    run_btree_test_cached(1, |mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }
    });
}

#[test]
fn cached_insert_get_cache_64() {
    let (key, value) = (u32::build, u32::build);
    run_btree_test_cached(64, |mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.get(&key(i)), Some(value(i)));
        }
    });
}

#[test]
fn cached_insert_overwrites_cache_1() {
    let (key, value) = (u32::build, u32::build);
    run_btree_test_cached(1, |mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.insert(key(i), value(i + 1)), Some(value(i)));
            assert_eq!(btree.get(&key(i)), Some(value(i + 1)));
        }
    });
}

#[test]
fn cached_insert_overwrites_cache_64() {
    let (key, value) = (u32::build, u32::build);
    run_btree_test_cached(64, |mut btree| {
        let n = 1_000;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
            assert_eq!(btree.insert(key(i), value(i + 1)), Some(value(i)));
            assert_eq!(btree.get(&key(i)), Some(value(i + 1)));
        }
    });
}

#[test]
fn cached_insert_remove_many_cache_1() {
    let (key, value) = (u32::build, u32::build);
    run_btree_test_cached(1, |mut btree| {
        let n = 500;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }
        for i in 0..n {
            assert_eq!(btree.remove(&key(i)), Some(value(i)));
        }
        assert!(btree.is_empty());
    });
}

#[test]
fn cached_insert_remove_many_cache_64() {
    let (key, value) = (u32::build, u32::build);
    run_btree_test_cached(64, |mut btree| {
        let n = 500;
        for i in 0..n {
            assert_eq!(btree.insert(key(i), value(i)), None);
        }
        for i in 0..n {
            assert_eq!(btree.remove(&key(i)), Some(value(i)));
        }
        assert!(btree.is_empty());
    });
}

#[test]
fn cached_pop_first_cache_1() {
    run_btree_test_cached(1, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
        }
        for i in 0..n {
            assert_eq!(btree.pop_first(), Some((i, i)));
        }
        assert!(btree.is_empty());
    });
}

#[test]
fn cached_pop_first_cache_64() {
    run_btree_test_cached(64, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
        }
        for i in 0..n {
            assert_eq!(btree.pop_first(), Some((i, i)));
        }
        assert!(btree.is_empty());
    });
}

#[test]
fn cached_pop_last_cache_1() {
    run_btree_test_cached(1, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
        }
        for i in (0..n).rev() {
            assert_eq!(btree.pop_last(), Some((i, i)));
        }
        assert!(btree.is_empty());
    });
}

#[test]
fn cached_pop_last_cache_64() {
    run_btree_test_cached(64, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
        }
        for i in (0..n).rev() {
            assert_eq!(btree.pop_last(), Some((i, i)));
        }
        assert!(btree.is_empty());
    });
}

#[test]
fn cached_first_key_value_cache_1() {
    run_btree_test_cached(1, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in (0..n).rev() {
            btree.insert(i, i);
            assert_eq!(btree.first_key_value(), Some((i, i)));
        }
    });
}

#[test]
fn cached_first_key_value_cache_64() {
    run_btree_test_cached(64, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in (0..n).rev() {
            btree.insert(i, i);
            assert_eq!(btree.first_key_value(), Some((i, i)));
        }
    });
}

#[test]
fn cached_last_key_value_cache_1() {
    run_btree_test_cached(1, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
            assert_eq!(btree.last_key_value(), Some((i, i)));
        }
    });
}

#[test]
fn cached_last_key_value_cache_64() {
    run_btree_test_cached(64, |mut btree: BTreeMap<u64, u64, _>| {
        let n = 200;
        for i in 0..n {
            btree.insert(i, i);
            assert_eq!(btree.last_key_value(), Some((i, i)));
        }
    });
}

// ---------------------------------------------------------------------------
// Cache metrics smoke tests
// ---------------------------------------------------------------------------

/// After getting N keys, the cache hit count must be > 0.
/// Clears metrics before the measured workload so counters reflect only gets.
#[test]
fn cache_metrics_nonzero_hits() {
    let mem = make_memory();
    let mut btree: BTreeMap<u64, u64, _> = BTreeMap::new(mem).with_node_cache(16);

    let n = 200u64;
    for i in 0..n {
        btree.insert(i, i);
    }

    // Clear counters accumulated during inserts.
    btree.node_cache_clear_metrics();

    // Workload: get all keys — traversal should hit cached upper-level nodes.
    for i in 0..n {
        assert_eq!(btree.get(&i), Some(i));
    }

    let metrics = btree.node_cache_metrics();
    assert!(
        metrics.hits() > 0,
        "Expected cache hits > 0 after {n} gets, got {:?}",
        metrics
    );
    assert!(
        metrics.hit_ratio() > 0.0,
        "Expected hit_ratio > 0 for get-heavy workload, got {:?}",
        metrics
    );
}

/// With cache disabled (0 slots), operations succeed and metrics show 0 hits.
#[test]
fn cache_disabled_metrics_zero() {
    let mem = make_memory();
    let mut btree: BTreeMap<u64, u64, _> = BTreeMap::new(mem).with_node_cache(0);

    for i in 0..100u64 {
        btree.insert(i, i);
    }

    btree.node_cache_clear_metrics();

    for i in 0..100u64 {
        assert_eq!(btree.get(&i), Some(i));
    }

    let metrics = btree.node_cache_metrics();
    assert_eq!(metrics.hits(), 0, "Disabled cache should have 0 hits");
    assert_eq!(metrics.misses(), 0, "Disabled cache should have 0 misses");
    assert_eq!(metrics.total(), 0, "Disabled cache should have 0 lookups");
}

/// After clear_new(), cache metrics should be reset.
#[test]
fn cache_metrics_reset_after_clear() {
    let mem = make_memory();
    let mut btree: BTreeMap<u64, u64, _> = BTreeMap::new(mem).with_node_cache(16);

    for i in 0..100u64 {
        btree.insert(i, i);
    }

    btree.node_cache_clear_metrics();

    for i in 0..100u64 {
        let _ = btree.get(&i);
    }
    let before = btree.node_cache_metrics();
    assert!(before.hits() > 0);

    btree.clear_new();

    let after = btree.node_cache_metrics();
    assert_eq!(after.hits(), 0, "Metrics should reset after clear_new");
    assert_eq!(after.misses(), 0, "Metrics should reset after clear_new");
    assert_eq!(after.total(), 0, "Metrics should reset after clear_new");
}
