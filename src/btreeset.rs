use crate::{btreemap::Iter as IterMap, BTreeMap, Memory, Storable};
use core::ops::RangeBounds;

#[cfg(test)]
mod proptests;

/// An iterator over the entries of a [`BTreeSet`].
pub struct Iter<'a, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    iter_internal: IterMap<'a, K, (), M>,
}

impl<'a, K, M> Iter<'a, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    fn new(iter: IterMap<'a, K, (), M>) -> Self {
        Iter {
            iter_internal: iter,
        }
    }
}

impl<K, M> Iterator for Iter<'_, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_internal.next().map(|(a, _)| a)
    }
}

/// This module implements a set based on a B-Tree
/// in stable memory.
///
/// # Overview
///
/// A `BTreeSet` is a "stable" set based on a B-tree. It is designed to work directly in stable memory,
/// allowing it to persist across upgrades and scale to large sizes.
///
/// The implementation is based on the algorithm outlined in "Introduction to Algorithms"
/// by Cormen et al.
///
/// ## Features
///
/// - **Efficient Operations**: Provides efficient insertion, deletion, and lookup operations.
/// - **Persistence**: Works directly in stable memory, persisting across upgrades.
/// - **Scalability**: Can scale to gigabytes in size.
///
/// ## Example
///
/// ```rust
/// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
///
/// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
///
/// set.insert(42);
/// assert!(set.contains(&42));
/// assert_eq!(set.pop_first(), Some(42));
/// assert!(set.is_empty());
/// ```
pub struct BTreeSet<K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    map: BTreeMap<K, (), M>,
}

impl<K, M> BTreeSet<K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    /// Initializes a `BTreeSet`.
    ///
    /// If the memory provided already contains a `BTreeSet`, then that
    /// map is loaded. Otherwise, a new `BTreeSet` instance is created.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let set: BTreeSet<u64, _> = BTreeSet::init(DefaultMemoryImpl::default());
    /// ```
    pub fn init(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::init(memory),
        }
    }

    /// Creates a new instance of a `BTreeSet`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// ```
    pub fn new(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::new(memory),
        }
    }

    /// Loads the set from memory.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    ///
    /// // Save the set to memory
    /// let memory = set.into_memory();
    ///
    /// // Load the set from memory
    /// let loaded_set: BTreeSet<u64, _> = BTreeSet::load(memory);
    /// assert!(loaded_set.contains(&42));
    /// ```
    pub fn load(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::load(memory),
        }
    }

    /// Inserts a key into the set. Returns `true` if the key
    /// did not exist in the set before.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// assert!(set.insert(42));
    /// assert!(!set.insert(42)); // Key already exists
    /// ```
    pub fn insert(&mut self, key: K) -> bool {
        self.map.insert(key, ()).is_none()
    }

    /// Returns `true` if the key exists in the set, `false` otherwise.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// assert!(set.contains(&42));
    /// assert!(!set.contains(&7));
    /// ```
    pub fn contains(&self, key: &K) -> bool {
        self.map.get(key).is_some()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// assert!(set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn len(&self) -> u64 {
        self.map.len()
    }

    /// Returns the underlying memory.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// let memory = set.into_memory();
    /// ```
    pub fn into_memory(self) -> M {
        self.map.into_memory()
    }

    /// Removes all elements from the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear_new();
    }

    /// Returns the first key in the set. This key
    /// is the minimum key in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.first(), Some(7));
    /// ```
    pub fn first(&self) -> Option<K> {
        self.map.first_key_value().map(|(a, _)| a)
    }

    /// Returns the last key in the set. This key
    /// is the maximum key in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.last(), Some(42));
    /// ```
    pub fn last(&self) -> Option<K> {
        self.map.last_key_value().map(|(a, _)| a)
    }

    /// Removes a key from the set, returning `true` if it exists.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// assert!(set.remove(&42));
    /// assert!(!set.contains(&42));
    /// ```
    pub fn remove(&mut self, key: &K) -> bool {
        self.map.remove(key).is_some()
    }

    /// Removes and returns the last element in the set. The key of this element is the maximum key that was in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.pop_last(), Some(42));
    /// ```
    pub fn pop_last(&mut self) -> Option<K> {
        self.map.pop_last().map(|(a, _)| a)
    }

    /// Removes and returns the first element in the set. The key of this element is the minimum key that was in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.pop_first(), Some(7));
    /// ```
    pub fn pop_first(&mut self) -> Option<K> {
        self.map.pop_first().map(|(a, _)| a)
    }

    /// Returns an iterator over the entries of the set, sorted by key.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(42);
    /// set.insert(7);
    /// for key in set.iter() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<K, M> {
        Iter::new(self.map.iter())
    }

    /// Returns an iterator over the entries in the set where keys
    /// belong to the specified range.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(1);
    /// set.insert(2);
    /// set.insert(3);
    /// let range: Vec<_> = set.range(2..).collect();
    /// assert_eq!(range, vec![2, 3]);
    /// ```
    pub fn range(&self, key_range: impl RangeBounds<K>) -> Iter<K, M> {
        Iter::new(self.map.range(key_range))
    }

    /// Returns an iterator pointing to the first element strictly below the given bound.
    /// Returns an empty iterator if there are no keys strictly below the given bound.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    ///
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(DefaultMemoryImpl::default());
    /// set.insert(1);
    /// set.insert(2);
    /// set.insert(3);
    ///
    /// let upper_bound: Option<u64> = set.iter_upper_bound(&3).next();
    /// assert_eq!(upper_bound, Some(2));
    /// ```
    pub fn iter_upper_bound(&self, bound: &K) -> Iter<K, M> {
        Iter::new(self.map.iter_upper_bound(bound))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::storable::Blob;
    use crate::VectorMemory;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// Creates a new shared memory instance.
    pub(crate) fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    pub(crate) fn b(x: &[u8]) -> Blob<10> {
        Blob::<10>::try_from(x).unwrap()
    }

    /// A test runner that runs the test using `BTreeSet`.
    pub fn run_btree_test<K, R, F>(f: F)
    where
        K: Storable + Ord + Clone,
        F: Fn(BTreeSet<K, VectorMemory>) -> R,
    {
        let mem = make_memory();
        let btree = BTreeSet::new(mem);
        f(btree);
    }

    #[test]
    fn init_preserves_data_set() {
        run_btree_test(|mut btree| {
            assert!(btree.insert(b(&[1, 2, 3])));
            assert!(btree.contains(&b(&[1, 2, 3])));

            // Reload the btree
            let btree = BTreeSet::init(btree.into_memory());

            // Data still exists.
            assert!(btree.contains(&b(&[1, 2, 3])));
        });
    }

    #[test]
    fn test_insert_and_contains() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        assert!(!btreeset.contains(&1u32));
        btreeset.insert(1u32);
        assert!(btreeset.contains(&1u32));
    }

    #[test]
    fn test_remove() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(1u32);
        assert!(btreeset.contains(&1u32));
        btreeset.remove(&1u32);
        assert!(!btreeset.contains(&1u32));
    }

    #[test]
    fn test_iter_upper_bound() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        for i in 0u32..100 {
            btreeset.insert(i);

            // Test that `iter_upper_bound` returns the largest element strictly below the bound.
            for j in 1u32..=i {
                assert_eq!(
                    btreeset.iter_upper_bound(&(j + 1)).next(),
                    Some(j),
                    "failed to get an upper bound for {}",
                    j + 1
                );
            }
            assert_eq!(
                btreeset.iter_upper_bound(&0).next(),
                None,
                "0 must not have an upper bound"
            );
        }
    }

    #[test]
    fn test_iter() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(1u32);
        btreeset.insert(2u32);
        btreeset.insert(3u32);

        let elements: Vec<_> = btreeset.iter().collect();
        assert_eq!(elements, vec![1u32, 2u32, 3u32]);
    }

    #[test]
    fn test_range() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        for i in 1u32..=10 {
            btreeset.insert(i);
        }

        let range: Vec<_> = btreeset.range(4u32..8u32).collect();
        assert_eq!(range, vec![4u32, 5u32, 6u32, 7u32]);
    }

    #[test]
    fn test_first_and_last() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(3u32);
        btreeset.insert(1u32);
        btreeset.insert(2u32);

        assert_eq!(btreeset.first(), Some(1u32));
        assert_eq!(btreeset.last(), Some(3u32));
    }

    #[test]
    fn test_len_and_is_empty() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        assert!(btreeset.is_empty());
        assert_eq!(btreeset.len(), 0);

        btreeset.insert(1u32);
        assert!(!btreeset.is_empty());
        assert_eq!(btreeset.len(), 1);
    }

    #[test]
    fn test_pop_first_and_last() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(3u32);
        btreeset.insert(1u32);
        btreeset.insert(2u32);

        assert_eq!(btreeset.pop_first(), Some(1u32));
        assert_eq!(btreeset.pop_last(), Some(3u32));
        assert_eq!(btreeset.len(), 1);
        assert_eq!(btreeset.first(), Some(2u32));
        assert_eq!(btreeset.last(), Some(2u32));
    }

    #[test]
    fn test_clear() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        btreeset.insert(1);
        btreeset.insert(2);
        btreeset.insert(3);

        assert_eq!(btreeset.len(), 3);
        btreeset.clear();
        assert!(btreeset.is_empty());
        assert_eq!(btreeset.len(), 0);
        assert_eq!(btreeset.iter().next(), None);
    }

    #[test]
    fn test_iterate_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1000 {
            btreeset.insert(i);
        }

        let elements: Vec<_> = btreeset.iter().collect();
        assert_eq!(elements.len(), 1000);
        assert_eq!(elements[0], 0);
        assert_eq!(elements[999], 999);
    }

    #[test]
    fn test_iter_upper_bound_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0u32..1000 {
            btreeset.insert(i);
        }

        assert_eq!(btreeset.iter_upper_bound(&500).next(), Some(499));
        assert_eq!(btreeset.iter_upper_bound(&0).next(), None);
        assert_eq!(btreeset.iter_upper_bound(&1000).next(), Some(999));
    }

    #[test]
    fn test_range_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0u32..1000 {
            btreeset.insert(i);
        }

        let range: Vec<_> = btreeset.range(100..200).collect();
        assert_eq!(range.len(), 100);
        assert_eq!(range[0], 100);
        assert_eq!(range[99], 199);
    }

    #[test]
    fn test_empty_set() {
        let mem = make_memory();
        let btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert!(btreeset.is_empty());
        assert_eq!(btreeset.len(), 0);
        assert_eq!(btreeset.first(), None);
        assert_eq!(btreeset.last(), None);
        assert_eq!(btreeset.iter().next(), None);
    }

    #[test]
    fn test_insert_duplicate() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert!(btreeset.insert(42));
        assert!(!btreeset.insert(42)); // Duplicate insert
        assert_eq!(btreeset.len(), 1);
        assert!(btreeset.contains(&42));
    }

    #[test]
    fn test_remove_nonexistent() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert!(!btreeset.remove(&42)); // Removing a non-existent element
        assert!(btreeset.is_empty());
    }

    #[test]
    fn test_pop_first_and_last_empty() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert_eq!(btreeset.pop_first(), None);
        assert_eq!(btreeset.pop_last(), None);
    }

    #[test]
    fn test_iter_upper_bound_empty() {
        let mem = make_memory();
        let btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert_eq!(btreeset.iter_upper_bound(&42u32).next(), None);
    }

    #[test]
    fn test_range_empty() {
        let mem = make_memory();
        let btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        let range: Vec<_> = btreeset.range(10..20).collect();
        assert!(range.is_empty());
    }

    #[test]
    fn test_insert_and_remove_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1_000 {
            assert!(btreeset.insert(i));
        }
        assert_eq!(btreeset.len(), 1_000);

        for i in 0..1_000 {
            assert!(btreeset.remove(&i));
        }
        assert!(btreeset.is_empty());
    }

    #[test]
    fn test_remove_nonexistent_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1_000 {
            assert!(btreeset.insert(i));
        }

        for i in 1_000..2_000 {
            assert!(!btreeset.remove(&i)); // Non-existent elements
        }
        assert_eq!(btreeset.len(), 1_000);
    }

    #[test]
    fn test_iterate_empty_set() {
        let mem = make_memory();
        let btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        let elements: Vec<_> = btreeset.iter().collect();
        assert!(elements.is_empty());
    }

    #[test]
    fn test_range_with_no_matches() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..10 {
            btreeset.insert(i);
        }

        let range: Vec<_> = btreeset.range(20..30).collect();
        assert!(range.is_empty());
    }

    #[test]
    fn test_clear_and_reuse() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..100 {
            btreeset.insert(i);
        }
        assert_eq!(btreeset.len(), 100);

        btreeset.clear();
        assert!(btreeset.is_empty());

        for i in 100..200 {
            btreeset.insert(i);
        }
        assert_eq!(btreeset.len(), 100);
        assert!(btreeset.contains(&150));
    }

    #[test]
    fn test_pop_first_and_last_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1_000 {
            btreeset.insert(i);
        }

        for i in 0..500 {
            assert_eq!(btreeset.pop_first(), Some(i));
        }

        for i in (500..1_000).rev() {
            assert_eq!(btreeset.pop_last(), Some(i));
        }

        assert!(btreeset.is_empty());
    }

    #[test]
    fn test_iter_upper_bound_edge_cases() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 1..=10 {
            btreeset.insert(i);
        }

        assert_eq!(btreeset.iter_upper_bound(&1).next(), None); // No element strictly below 1
        assert_eq!(btreeset.iter_upper_bound(&5).next(), Some(4)); // Largest element below 5
        assert_eq!(btreeset.iter_upper_bound(&11).next(), Some(10)); // Largest element below 11
    }
}
