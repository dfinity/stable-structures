use crate::{btreemap::Iter, BTreeMap, Memory, Storable};
use core::ops::RangeBounds;

/// An iterator over the entries of a [`BTreeMap`].
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct IterSet<'a, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    iter_internal: Iter<'a, K, (), M>,
}

impl<'a, K, M> IterSet<'a, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    fn new(iter: Iter<'a, K, (), M>) -> Self {
        IterSet {
            iter_internal: iter,
        }
    }
}

impl<K, M> Iterator for IterSet<'_, K, M>
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
        self.map.insert(key, ()) == None
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
        self.map.remove(key) != None
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
    pub fn iter(&self) -> IterSet<K, M> {
        IterSet::new(self.map.iter())
    }

    /// Returns an iterator over the entries in the set where keys
    /// belong to the specified range.
    pub fn range(&self, key_range: impl RangeBounds<K>) -> IterSet<K, M> {
        IterSet::new(self.map.range(key_range))
    }

    /// Returns an iterator pointing to the first element below the given bound.
    /// Returns an empty iterator if there are no keys below the given bound.
    pub fn iter_upper_bound(&self, bound: &K) -> IterSet<K, M> {
        IterSet::new(self.map.iter_upper_bound(bound))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        storable::{Blob, Bound as StorableBound},
        VectorMemory,
    };
    use std::cell::RefCell;
    use std::rc::Rc;

    pub(crate) fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    // A helper method to succinctly create an entry.
    fn e(x: u8) -> (Blob<10>, Vec<u8>) {
        (b(&[x]), vec![])
    }

    pub(crate) fn b(x: &[u8]) -> Blob<10> {
        Blob::<10>::try_from(x).unwrap()
    }

    // A test runner that runs the test using both V1 and V2 btrees.
    pub fn btree_test<K, R, F>(f: F)
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
        btree_test(|mut btree| {
            assert!(btree.insert(b(&[1, 2, 3])));
            assert!(btree.contains_key(&b(&[1, 2, 3])));

            // Reload the btree
            let btree = BTreeSet::init(btree.into_memory());

            // Data still exists.
            assert!(btree.contains_key(&b(&[1, 2, 3])));
        });
    }
}
