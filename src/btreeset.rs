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

/// A "stable" set based on a B-tree.
///
/// The implementation is based on the algorithm outlined in "Introduction to Algorithms"
/// by Cormen et al.
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
    pub fn init(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::init(memory),
        }
    }

    /// Creates a new instance a `BTreeSet`.
    pub fn new(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::new(memory),
        }
    }

    /// Loads the set from memory.
    pub fn load(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::load(memory),
        }
    }

    /// Inserts a key into the set. Returns true if key
    /// did not exist in the set before.
    pub fn insert(&mut self, key: K) -> bool {
        self.map.insert(key, ()).is_none()
    }

    /// Returns `true` if the key exists in the map, `false` otherwise.
    pub fn contains_key(&self, key: &K) -> bool {
        self.map.get(key).is_some()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> u64 {
        self.map.len()
    }

    /// Returns the underlying memory.
    pub fn into_memory(self) -> M {
        self.map.into_memory()
    }

    /// Removes all elements from the set.
    pub fn clear(&mut self) {
        self.map.clear_new();
    }

    /// Returns the first key in the map. This key
    /// is the minimum key in the map.
    pub fn first_key(&self) -> Option<K> {
        self.map.first_key_value().map(|(a, _)| a)
    }

    /// Returns the last key in the set. This key
    /// is the maximum key in the set.
    pub fn last_key(&self) -> Option<K> {
        self.map.last_key_value().map(|(a, _)| a)
    }

    /// Removes a key from the map, returning true if it exists.
    pub fn remove(&mut self, key: &K) -> bool {
        self.map.remove(key).is_some()
    }

    /// Removes and returns the last element in the set. The key of this element is the maximum key that was in the set.
    pub fn pop_last(&mut self) -> Option<K> {
        self.map.pop_last().map(|(a, _)| a)
    }

    /// Removes and returns the first element in the set. The key of this element is the minimum key that was in the set.
    pub fn pop_first(&mut self) -> Option<K> {
        self.map.pop_first().map(|(a, _)| a)
    }

    /// Returns an iterator over the entries of the set, sorted by key.
    pub fn iter(&self) -> Iter<K, M> {
        Iter::new(self.map.iter())
    }

    /// Returns an iterator over the entries in the set where keys
    /// belong to the specified range.
    pub fn range(&self, key_range: impl RangeBounds<K>) -> Iter<K, M> {
        Iter::new(self.map.range(key_range))
    }

    /// Returns an iterator pointing to the first element below the given bound.
    /// Returns an empty iterator if there are no keys below the given bound.
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
            assert!(btree.contains_key(&b(&[1, 2, 3])));

            // Reload the btree
            let btree = BTreeSet::init(btree.into_memory());

            // Data still exists.
            assert!(btree.contains_key(&b(&[1, 2, 3])));
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// Creates a new shared memory instance.
    pub(crate) fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn test_insert_and_contains() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        assert!(!btreeset.contains_key(&1u32));
        btreeset.insert(1u32);
        assert!(btreeset.contains_key(&1u32));
    }

    #[test]
    fn test_remove() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(1u32);
        assert!(btreeset.contains_key(&1u32));
        btreeset.remove(&1u32);
        assert!(!btreeset.contains_key(&1u32));
    }

    #[test]
    fn test_iter_upper_bound() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        for i in 0u32..100 {
            btreeset.insert(i);
            for j in 0u32..=i {
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

        assert_eq!(btreeset.first_key(), Some(1u32));
        assert_eq!(btreeset.last_key(), Some(3u32));
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
    }

    #[test]
    fn test_clear() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(1u32);
        btreeset.insert(2u32);
        btreeset.clear();

        assert!(btreeset.is_empty());
        assert_eq!(btreeset.len(), 0);
    }

    #[test]
    fn test_range_various_prefixes() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        for i in [
            1u32, 2u32, 3u32, 4u32, 11u32, 12u32, 13u32, 14u32, 21u32, 22u32, 23u32, 24u32,
        ] {
            btreeset.insert(i);
        }

        let range: Vec<_> = btreeset.range(10u32..20u32).collect();
        assert_eq!(range, vec![11u32, 12u32, 13u32, 14u32]);

        let range: Vec<_> = btreeset.range(0u32..10u32).collect();
        assert_eq!(range, vec![1u32, 2u32, 3u32, 4u32]);

        let range: Vec<_> = btreeset.range(20u32..30u32).collect();
        assert_eq!(range, vec![21u32, 22u32, 23u32, 24u32]);
    }
}
