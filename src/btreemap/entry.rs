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
//! For the same reason there is no equivalent of the standard library's `get_mut` or
//! `into_mut`. Use [`OccupiedEntry::and_modify`], which reads the value, hands it to your
//! closure, and writes it back.
//!
//! # `entry` writes to stable memory
//!
//! [`BTreeMap::entry`] splits full nodes on the way down so that a later insert can finish
//! in one pass. It therefore writes — allocating nodes and rewriting the header — even for
//! a key that turns out to be present, and even if the entry is dropped unused. The cost is
//! bounded (each node splits at most once, and that split was coming on the next insert
//! anyway), but prefer [`BTreeMap::get`] when you only mean to read. See
//! [`BTreeMap::entry`] for details.
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

/// A loaded node together with the index of one slot inside it: for an
/// [`OccupiedEntry`] the slot holding the entry, for a [`VacantEntry`] the slot the key
/// would occupy. `depth` is the node's distance from the root, which the node cache's
/// eviction policy needs.
///
/// The node itself is kept, rather than just its address, so that reading and writing
/// through an entry needs no further node loads. [`BTreeMap::entry`] takes the node out
/// of the map's node cache; it is put back only where that is both useful and cheap (see
/// [`OccupiedEntry::remove`]). Mutating an entry saves the node, which invalidates its
/// cache slot — a just-saved node holds every one of its keys and values materialized,
/// so returning it to the cache in that state would waste heap.
pub(crate) struct NodeSlot<K: Storable + Ord + Clone> {
    pub(crate) node: Node<K>,
    pub(crate) idx: usize,
    pub(crate) depth: u8,
}

impl<K: Storable + Ord + Clone> NodeSlot<K> {
    pub(crate) fn new(node: Node<K>, idx: usize, depth: u8) -> Self {
        Self { node, idx, depth }
    }
}

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
    pub(crate) slot: Option<NodeSlot<K>>,
}

/// A view into an occupied entry in a [`BTreeMap`].
///
/// Obtained from [`Entry::Occupied`] or as the result of [`VacantEntry::insert`].
pub struct OccupiedEntry<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> {
    pub(crate) map: &'a mut BTreeMap<K, V, M>,
    pub(crate) key: K,
    pub(crate) slot: NodeSlot<K>,
}

/// A value returned by [`OccupiedEntry::insert`] or [`OccupiedEntry::remove`] that has not
/// yet been deserialized.
///
/// Deserialization is deferred so that callers who do not need the previous value pay no
/// decode cost. Call [`into_value`](LazyValue::into_value) to obtain the concrete `T`.
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
///     // Discard the old value without deserializing it.
///     let _old: _ = e.insert(99);
/// }
///
/// if let Entry::Occupied(e) = map.entry(1) {
///     // Deserialize only when the value is actually needed.
///     let old_value = e.insert(0).into_value();
///     assert_eq!(old_value, 99);
/// }
/// ```
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
                let val = default(entry.key());
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
    ///
    /// # Panics
    ///
    /// Panics if the serialized key or value exceeds the maximum size of its type, exactly
    /// as [`BTreeMap::insert`] does. Note that [`BTreeMap::entry`] may already have split
    /// nodes by this point; the map is left valid and consistent, but not necessarily in
    /// the shape it had before `entry` was called.
    pub fn insert(self, value: V) -> OccupiedEntry<'a, K, V, M> {
        let Self { map, key, slot } = self;
        let slot = match slot {
            Some(mut slot) => {
                slot.node
                    .insert_entry(slot.idx, (key.clone(), value.into_bytes_checked()));
                map.save_node(&mut slot.node);
                map.length += 1;
                map.save_header();
                slot
            }
            None => {
                // The map was empty when `entry()` was called. Delegate to the regular
                // insert path, which handles allocating the root, then point the new
                // `OccupiedEntry` at the root node's first slot.
                map.insert(key.clone(), value);
                let node = map.take_or_load_node(map.root_addr);
                NodeSlot::new(node, 0, 0)
            }
        };
        OccupiedEntry { map, key, slot }
    }
}

impl<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> OccupiedEntry<'a, K, V, M> {
    /// Returns a reference to the key stored in the map.
    ///
    /// As in the standard library, this is the key already held by the map, not the one
    /// passed to [`BTreeMap::entry`]. The two compare equal, but they can differ in ways
    /// `Ord` does not see — for example a `K` whose ordering ignores some of its fields.
    pub fn key(&self) -> &K {
        self.slot.node.key(self.slot.idx, self.map.memory())
    }

    /// Consumes the entry and returns the key stored in the map.
    ///
    /// Like [`key`](Self::key), this is the map's own key rather than the one passed to
    /// [`BTreeMap::entry`].
    pub fn into_key(self) -> K {
        self.key().clone()
    }

    /// Returns the current value associated with this entry.
    ///
    /// Every call re-reads the value from stable memory and deserializes it; the result is
    /// not memoized. Bind it to a local if you need it more than once.
    pub fn get(&self) -> V {
        // Read straight out of the node the entry already holds — no load required.
        // The read is uncached so that repeated reads don't inflate the node with a
        // materialized value buffer.
        let value_bytes = self
            .slot
            .node
            .read_value_uncached(self.slot.idx, self.map.memory());
        V::from_bytes(Cow::Owned(value_bytes))
    }

    /// Provides in-place mutable access to the value in this occupied entry.
    ///
    /// Reads the current value, calls `f` with a mutable reference to it, then writes the
    /// modified value back. Returns `self` so the call can be chained.
    ///
    /// The write is unconditional: the value is re-serialized and the node saved even if
    /// `f` left it untouched.
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
        self.write_value(value);
        self
    }

    /// Overwrites the value in this entry's slot, returning the old bytes.
    ///
    /// `update_value` saves the node, which invalidates its cache slot. The node is
    /// deliberately not put back into the cache: a just-saved node holds every one of
    /// its keys and values materialized, so caching it in that state would waste heap.
    fn write_value(&mut self, value: V) -> Vec<u8> {
        self.map.update_value(
            &mut self.slot.node,
            self.slot.idx,
            value.into_bytes_checked(),
        )
    }

    /// Replaces the current value with `value` and returns the previous value as a
    /// [`LazyValue`], which is only deserialized if you call [`LazyValue::into_value`].
    ///
    /// # Panics
    ///
    /// Panics if the serialized `value` exceeds the maximum size of `V`, exactly as
    /// [`BTreeMap::insert`] does. The map is left unmodified in that case.
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
    ///     let old = e.insert(99).into_value();
    ///     assert_eq!(old, 10);
    /// }
    /// assert_eq!(map.get(&1), Some(99));
    /// ```
    pub fn insert(mut self, value: V) -> LazyValue<V> {
        LazyValue::new(self.write_value(value))
    }

    /// Removes the entry from the map and returns the stored value as a [`LazyValue`], which
    /// is only deserialized if you call [`LazyValue::into_value`].
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
    ///     assert_eq!(e.remove().into_value(), 42);
    /// }
    /// assert!(map.is_empty());
    /// ```
    pub fn remove(self) -> LazyValue<V> {
        let Self { map, key, slot } = self;
        let NodeSlot {
            mut node,
            idx,
            depth,
        } = slot;
        let bytes = match node.node_type() {
            NodeType::Leaf if node.can_remove_entry_without_merging() => {
                // Fast path: the leaf has enough entries to remove without merging.
                let value = node.remove_entry(idx, map.memory()).1;
                // `can_remove_entry_without_merging` guarantees the leaf held more than
                // the minimum number of entries, so it cannot be empty after removal.
                debug_assert!(node.entries_len() > 0);
                map.save_node(&mut node);
                map.length -= 1;
                map.save_header();
                value
            }
            _ => {
                // Slow path: the removal may require rebalancing/merging, so do a fresh
                // traversal from the root. The node is unmodified, so return it to the
                // cache first — the traversal can then take it from there rather than
                // re-reading it from memory.
                map.return_node(node, depth);
                let root = map.take_or_load_node(map.root_addr);
                map.remove_helper(root, &key, 0).expect("key must exist")
            }
        };
        LazyValue::new(bytes)
    }
}

impl<T: Storable> LazyValue<T> {
    pub(crate) fn new(bytes: Vec<u8>) -> Self {
        LazyValue {
            bytes,
            phantom_data: PhantomData,
        }
    }

    /// Deserializes and returns the value.
    pub fn into_value(self) -> T {
        T::from_bytes(Cow::Owned(self.bytes))
    }
}

// The `Debug` impls below print keys only. Values are deliberately left out: reading one
// means a stable-memory read and a deserialization, which is not what anyone expects a
// `Debug` impl to do.

impl<K: Storable + Ord + Clone + std::fmt::Debug, V: Storable, M: Memory> std::fmt::Debug
    for Entry<'_, K, V, M>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Entry::Vacant(entry) => f.debug_tuple("Entry::Vacant").field(entry).finish(),
            Entry::Occupied(entry) => f.debug_tuple("Entry::Occupied").field(entry).finish(),
        }
    }
}

impl<K: Storable + Ord + Clone + std::fmt::Debug, V: Storable, M: Memory> std::fmt::Debug
    for VacantEntry<'_, K, V, M>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VacantEntry")
            .field("key", self.key())
            .finish()
    }
}

impl<K: Storable + Ord + Clone + std::fmt::Debug, V: Storable, M: Memory> std::fmt::Debug
    for OccupiedEntry<'_, K, V, M>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .finish()
    }
}

impl<T: Storable> std::fmt::Debug for LazyValue<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The value is intentionally not deserialized here.
        f.debug_struct("LazyValue")
            .field("num_bytes", &self.bytes.len())
            .finish()
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

    /// A key whose ordering ignores `tag`, so two keys can be `Ord`-equal while holding
    /// different bytes. Used to tell the stored key apart from the one passed to `entry`.
    #[derive(Clone, Debug)]
    struct TaggedKey {
        id: u32,
        tag: u8,
    }

    impl PartialEq for TaggedKey {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }
    impl Eq for TaggedKey {}
    impl PartialOrd for TaggedKey {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for TaggedKey {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.id.cmp(&other.id)
        }
    }
    impl Storable for TaggedKey {
        fn to_bytes(&self) -> Cow<'_, [u8]> {
            let mut bytes = self.id.to_be_bytes().to_vec();
            bytes.push(self.tag);
            Cow::Owned(bytes)
        }
        fn into_bytes(self) -> Vec<u8> {
            self.to_bytes().into_owned()
        }
        fn from_bytes(bytes: Cow<'_, [u8]>) -> Self {
            Self {
                id: u32::from_be_bytes(bytes[0..4].try_into().unwrap()),
                tag: bytes[4],
            }
        }
        const BOUND: crate::storable::Bound = crate::storable::Bound::Bounded {
            max_size: 5,
            is_fixed_size: true,
        };
    }

    /// `OccupiedEntry::key` must report the key held by the map, like the std lib does,
    /// not the `Ord`-equal one that was passed to `entry`.
    #[test]
    fn occupied_entry_reports_the_stored_key() {
        let mut map: BTreeMap<TaggedKey, u32, _> = BTreeMap::new(Rc::new(RefCell::new(Vec::new())));
        map.insert(TaggedKey { id: 1, tag: 7 }, 100);

        let Entry::Occupied(e) = map.entry(TaggedKey { id: 1, tag: 99 }) else {
            panic!("key 1 is present");
        };
        assert_eq!(e.key().tag, 7, "`key` must return the stored key");
        assert_eq!(e.into_key().tag, 7, "`into_key` must return the stored key");

        // Overwriting the value must leave the stored key alone, also matching the std lib.
        if let Entry::Occupied(e) = map.entry(TaggedKey { id: 1, tag: 42 }) {
            e.insert(101);
        }
        assert_eq!(map.iter().next().unwrap().key().tag, 7);

        // A vacant entry has no stored key, so it reports the one it was given.
        let Entry::Vacant(e) = map.entry(TaggedKey { id: 2, tag: 55 }) else {
            panic!("key 2 is absent");
        };
        assert_eq!(e.key().tag, 55);
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
    fn entry_uses_the_node_cache_along_the_path() {
        let mut map = new_map().with_node_cache(32);
        for i in 0u32..1000 {
            map.insert(i, i);
        }

        // Warm the cache along the path, then probe the same key again: the nodes on
        // the way down are taken from the cache and put back by the traversal, so the
        // second probe hits rather than re-reading them from memory.
        let _ = map.entry(500);
        map.node_cache_reset_metrics();
        let _ = map.entry(500);
        assert!(map.node_cache_metrics().hits() > 0);

        // The same holds for a vacant entry dropped without inserting, and the map is
        // unchanged by the probe.
        let _ = map.entry(5000);
        map.node_cache_reset_metrics();
        let _ = map.entry(5000);
        assert!(map.node_cache_metrics().hits() > 0);
        assert_eq!(map.get(&5000), None);
    }

    #[test]
    fn reading_and_writing_through_an_entry_needs_no_further_loads() {
        let mut map = new_map().with_node_cache(32);
        for i in 0u32..1000 {
            map.insert(i, i);
        }

        let Entry::Occupied(e) = map.entry(500) else {
            panic!();
        };
        // The entry holds its node, so reading and writing through it touch the cache
        // not at all — no lookups, hence no loads from memory.
        e.map.node_cache_reset_metrics();
        assert_eq!(e.get(), 500);
        let e = e.and_modify(|v| *v += 1);
        assert_eq!(e.get(), 501);
        assert_eq!(e.map.node_cache_metrics().total(), 0);

        assert_eq!(map.get(&500), Some(501));
    }

    #[test]
    fn entry_mutations_do_not_leave_stale_nodes_in_cache() {
        let mut map = new_map().with_node_cache(32);
        for i in 0u32..1000 {
            map.insert(i, i);
        }
        for i in 0u32..1000 {
            // Warm the cache along the key's path, mutate through the entry API,
            // then read back through the cached path.
            assert_eq!(map.get(&i), Some(i));
            map.entry(i).and_modify(|v| *v += 1);
            assert_eq!(map.get(&i), Some(i + 1));
        }
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
