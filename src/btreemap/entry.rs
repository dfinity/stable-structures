//! Entry API for [`BTreeMap`].
//!
//! This module provides the [`Entry`] type, which gives efficient in-place access to a map's
//! entries, allowing inspection or modification without redundant key lookups. The API mirrors
//! [`std::collections::btree_map::Entry`] as closely as the stable-memory model allows.
//!
//! # Note on `or_insert` return type
//!
//! The standard library's `or_insert` returns `&mut V`, giving a direct reference into the
//! map. Because values in this [`BTreeMap`] live in stable memory, long-lived references are
//! not possible. Instead, `or_insert` (and its variants) return an [`OccupiedEntry`], which
//! lets you continue reading or modifying the entry without a second key lookup.
//!
//! # Examples
//!
//! ```rust
//! use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
//!
//! let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
//!
//! // Insert a value only when the key is absent.
//! map.entry(1).or_insert(42);
//! assert_eq!(map.get(&1), Some(42));
//!
//! // Increment a counter, seeding it to 1 if absent.
//! map.entry(1).and_modify(|v| *v += 1).or_insert(1);
//! assert_eq!(map.get(&1), Some(43));
//! ```

use crate::btreemap::node::{Node, NodeType};
use crate::{BTreeMap, Memory, Storable};
use std::borrow::Cow;
use std::marker::PhantomData;

/// A view into a single entry of a [`BTreeMap`], which may either be occupied or vacant.
///
/// This type is returned by [`BTreeMap::entry`].
pub enum Entry<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> {
    /// A vacant entry: the key is not present in the map.
    Vacant(VacantEntry<'a, K, V, M>),
    /// An occupied entry: the key is already present in the map.
    Occupied(OccupiedEntry<'a, K, V, M>),
}

/// A view into a vacant entry in a [`BTreeMap`].
///
/// Obtained from [`Entry::Vacant`].
pub struct VacantEntry<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> {
    pub(crate) map: &'a mut BTreeMap<K, V, M>,
    pub(crate) key: K,
    /// Pre-computed insertion point from [`BTreeMap::entry`].
    ///
    /// `None` when the map was empty at the time `entry` was called — the root
    /// node had not yet been allocated, so we defer the full insert to
    /// [`VacantEntry::insert`] to avoid corrupting the map if this entry is
    /// dropped without inserting.
    pub(crate) location: Option<(Node<K>, usize)>,
}

/// A view into an occupied entry in a [`BTreeMap`].
///
/// Obtained from [`Entry::Occupied`] or as the result of [`VacantEntry::insert`].
pub struct OccupiedEntry<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> {
    pub(crate) map: &'a mut BTreeMap<K, V, M>,
    pub(crate) key: K,
    pub(crate) node: Node<K>,
    pub(crate) idx: usize,
}

pub struct LazyValue<T: Storable> {
    bytes: Vec<u8>,
    phantom_data: PhantomData<T>,
}

impl<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> Entry<'a, K, V, M> {
    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Consumes the entry and returns its key.
    pub fn into_key(self) -> K {
        match self {
            Entry::Occupied(entry) => entry.into_key(),
            Entry::Vacant(entry) => entry.into_key(),
        }
    }

    /// Ensures a value is present by inserting `default` if the entry is vacant, then returns
    /// an [`OccupiedEntry`] for further operations.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// assert_eq!(map.entry(1).or_insert(10).get(), 10);
    /// assert_eq!(map.entry(1).or_insert(99).get(), 10); // already present
    /// ```
    pub fn or_insert(self, default: V) -> OccupiedEntry<'a, K, V, M> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is present by inserting the result of `default` if the entry is vacant,
    /// then returns an [`OccupiedEntry`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// map.entry(1).or_insert_with(|| 42u32);
    /// assert_eq!(map.get(&1), Some(42));
    /// ```
    pub fn or_insert_with(self, default: impl FnOnce() -> V) -> OccupiedEntry<'a, K, V, M> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is present by inserting the result of `default`, called with the
    /// entry's key, if the entry is vacant. Returns an [`OccupiedEntry`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// map.entry(7).or_insert_with_key(|&k| k * 2);
    /// assert_eq!(map.get(&7), Some(14));
    /// ```
    pub fn or_insert_with_key(self, default: impl FnOnce(&K) -> V) -> OccupiedEntry<'a, K, V, M> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => {
                let val = default(&entry.key);
                entry.insert(val)
            }
        }
    }

    /// Ensures a value is present by inserting `V::default()` if the entry is vacant, then
    /// returns an [`OccupiedEntry`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// map.entry(1).or_default();
    /// assert_eq!(map.get(&1), Some(0u32));
    /// ```
    pub fn or_default(self) -> OccupiedEntry<'a, K, V, M>
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts
    /// via `or_insert` and friends.
    ///
    /// If the entry is vacant the closure is not called and the entry is returned unchanged,
    /// making it possible to chain with `or_insert` and friends.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// map.insert(1, 10);
    ///
    /// // Increment existing value, or seed with 1 for a new key.
    /// map.entry(1).and_modify(|v| *v += 1).or_insert(1);
    /// assert_eq!(map.get(&1), Some(11));
    ///
    /// map.entry(2).and_modify(|v| *v += 1).or_insert(1);
    /// assert_eq!(map.get(&2), Some(1));
    /// ```
    pub fn and_modify(self, f: impl FnOnce(&mut V)) -> Self {
        match self {
            Entry::Occupied(entry) => Entry::Occupied(entry.and_modify(f)),
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> VacantEntry<'a, K, V, M> {
    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Consumes the entry and returns its key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Inserts `value` into the map at this entry's key and returns an [`OccupiedEntry`]
    /// pointing at the newly inserted value.
    pub fn insert(self, value: V) -> OccupiedEntry<'a, K, V, M> {
        match self.location {
            Some((mut node, idx)) => {
                node.insert_entry(idx, (self.key.clone(), value.into_bytes_checked()));
                self.map.save_node(&mut node);
                self.map.length += 1;
                self.map.save_header();
                OccupiedEntry {
                    map: self.map,
                    key: self.key,
                    node,
                    idx,
                }
            }
            None => {
                // The map was empty when `entry()` was called. Delegate to the regular
                // insert path which handles root allocation, then find the new entry.
                let map = self.map;
                let key = self.key;
                map.insert(key.clone(), value);
                let (node, result) = map.find_node_for_insert(&key);
                let idx = result.expect("key was just inserted");
                OccupiedEntry {
                    map,
                    key,
                    node,
                    idx,
                }
            }
        }
    }
}

impl<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> OccupiedEntry<'a, K, V, M> {
    /// Returns a reference to the entry's key.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Consumes the entry and returns its key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Returns the current value associated with this entry.
    pub fn get(&self) -> V {
        let value_bytes = self.node.value(self.idx, self.map.memory());
        V::from_bytes(Cow::Borrowed(value_bytes))
    }

    /// Provides in-place mutable access to the value in this occupied entry.
    ///
    /// Reads the current value, calls `f` with a mutable reference to it, then writes the
    /// modified value back. Returns `self` so the call can be chained.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl, btreemap::entry::Entry};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// map.insert(1, 10);
    ///
    /// if let Entry::Occupied(e) = map.entry(1) {
    ///     e.and_modify(|v| *v *= 2);
    /// }
    /// assert_eq!(map.get(&1), Some(20));
    /// ```
    pub fn and_modify(mut self, f: impl FnOnce(&mut V)) -> Self {
        let mut value = self.get();
        f(&mut value);
        self.map
            .update_value(&mut self.node, self.idx, value.into_bytes_checked());
        self
    }

    /// Replaces the current value with `value` and returns the previous value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl, btreemap::entry::Entry};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// map.insert(1, 10);
    ///
    /// if let Entry::Occupied(e) = map.entry(1) {
    ///     let old = e.insert(99);
    ///     assert_eq!(old, 10);
    /// }
    /// assert_eq!(map.get(&1), Some(99));
    /// ```
    pub fn insert(mut self, value: V) -> LazyValue<V> {
        let old_bytes = self
            .map
            .update_value(&mut self.node, self.idx, value.into_bytes_checked());
        LazyValue::new(old_bytes)
    }

    /// Removes the entry from the map and returns the value that was stored.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl, btreemap::entry::Entry};
    ///
    /// let mut map: BTreeMap<u32, u32, _> = BTreeMap::new(DefaultMemoryImpl::default());
    /// map.insert(1, 42);
    ///
    /// if let Entry::Occupied(e) = map.entry(1) {
    ///     assert_eq!(e.remove(), 42);
    /// }
    /// assert!(map.is_empty());
    /// ```
    pub fn remove(self) -> LazyValue<V> {
        let bytes = match self.node.node_type() {
            NodeType::Leaf if self.node.can_remove_entry_without_merging() => {
                self.map.remove_from_leaf_node(self.node, self.idx)
            }
            NodeType::Leaf => {
                // TODO: avoid this slow path
                let root = self.map.load_node(self.map.root_addr);
                self.map
                    .remove_helper(root, &self.key)
                    .expect("key must exist")
            }
            NodeType::Internal => self
                .map
                .remove_from_internal_node(self.node, self.idx, &self.key),
        };
        LazyValue::new(bytes)
    }
}

impl<T: Storable> LazyValue<T> {
    pub fn new(bytes: Vec<u8>) -> Self {
        LazyValue {
            bytes,
            phantom_data: PhantomData,
        }
    }

    pub fn into_value(self) -> T {
        T::from_bytes(Cow::Owned(self.bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn new_map() -> BTreeMap<u32, u32, Rc<RefCell<Vec<u8>>>> {
        BTreeMap::new(Rc::new(RefCell::new(Vec::new())))
    }

    #[test]
    fn entry_end_to_end() {
        let mut map = new_map();

        for i in 0u32..100 {
            let Entry::Vacant(e) = map.entry(i) else {
                panic!();
            };
            e.insert(i);
        }

        for i in 0u32..100 {
            let Entry::Occupied(e) = map.entry(i) else {
                panic!();
            };
            assert_eq!(i, e.get());
            let old = e.insert(i + 1).into_value();
            assert_eq!(old, i);
        }

        for i in 0u32..100 {
            let Entry::Occupied(e) = map.entry(i) else {
                panic!();
            };
            assert_eq!(i + 1, e.get());
            let removed = e.remove().into_value();
            assert_eq!(removed, i + 1);
        }

        assert!(map.is_empty());
    }

    #[test]
    fn or_insert_vacant() {
        let mut map = new_map();
        assert_eq!(map.entry(1).or_insert(42).get(), 42);
        assert_eq!(map.get(&1), Some(42));
    }

    #[test]
    fn or_insert_occupied() {
        let mut map = new_map();
        map.insert(1, 10);
        assert_eq!(map.entry(1).or_insert(99).get(), 10); // default ignored
    }

    #[test]
    fn or_insert_with() {
        let mut map = new_map();
        map.entry(1).or_insert_with(|| 7u32);
        assert_eq!(map.get(&1), Some(7));
        // closure is not called when key is present
        map.entry(1)
            .or_insert_with(|| panic!("should not be called"));
        assert_eq!(map.get(&1), Some(7));
    }

    #[test]
    fn or_insert_with_key() {
        let mut map = new_map();
        map.entry(6).or_insert_with_key(|&k| k * 3);
        assert_eq!(map.get(&6), Some(18));
    }

    #[test]
    fn or_default() {
        let mut map = new_map();
        map.entry(1).or_default();
        assert_eq!(map.get(&1), Some(0u32));
    }

    #[test]
    fn and_modify_occupied() {
        let mut map = new_map();
        map.insert(1, 10);
        map.entry(1).and_modify(|v| *v += 5);
        assert_eq!(map.get(&1), Some(15));
    }

    #[test]
    fn and_modify_vacant() {
        let mut map = new_map();
        // closure must not be called; map must stay empty
        map.entry(1).and_modify(|_| panic!("should not be called"));
        assert_eq!(map.get(&1), None);
    }

    #[test]
    fn and_modify_then_or_insert() {
        let mut map = new_map();
        map.insert(1, 10u32);

        map.entry(1).and_modify(|v| *v += 1).or_insert(1);
        assert_eq!(map.get(&1), Some(11));

        map.entry(2).and_modify(|v| *v += 1).or_insert(1);
        assert_eq!(map.get(&2), Some(1));
    }

    #[test]
    fn occupied_insert_returns_old_value() {
        let mut map = new_map();
        map.insert(1, 10);
        let Entry::Occupied(e) = map.entry(1) else {
            panic!();
        };
        assert_eq!(e.insert(99).into_value(), 10);
        assert_eq!(map.get(&1), Some(99));
    }

    #[test]
    fn occupied_remove_returns_value() {
        let mut map = new_map();
        map.insert(1, 42);
        let Entry::Occupied(e) = map.entry(1) else {
            panic!();
        };
        assert_eq!(e.remove().into_value(), 42);
        assert!(map.is_empty());
    }

    #[test]
    fn or_insert_on_empty_map_then_drop() {
        // Dropping a VacantEntry on an empty map without inserting must not corrupt the map.
        let mut map = new_map();
        map.entry(1).and_modify(|_| panic!("should not be called"));
        assert_eq!(map.get(&1), None);
        // The map must still be usable after the drop.
        map.insert(1, 99);
        assert_eq!(map.get(&1), Some(99));
    }
}
