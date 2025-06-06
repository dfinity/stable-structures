use crate::{
    btreemap::Allocator,
    read_struct, read_to_vec, read_u32, read_u64, read_u64_vec,
    storable::Storable,
    types::{Address, Bytes},
    write, write_struct, write_u32, Memory,
};
use std::borrow::{Borrow, Cow};
use std::cell::OnceCell;

mod io;
#[cfg(test)]
mod tests;
mod v1;
mod v2;

use io::NodeReader;

// The minimum degree to use in the btree.
// This constant is taken from Rust's std implementation of BTreeMap.
const B: usize = 6;
// The maximum number of entries per node.
const CAPACITY: usize = 2 * B - 1;
const LAYOUT_VERSION_1: u8 = 1;
const LAYOUT_VERSION_2: u8 = 2;
const MAGIC: &[u8; 3] = b"BTN";
const LEAF_NODE_TYPE: u8 = 0;
const INTERNAL_NODE_TYPE: u8 = 1;
// The size of u32 in bytes.
const U32_SIZE: Bytes = Bytes::new(4);

#[derive(Debug, PartialEq, Copy, Clone, Eq)]
#[cfg_attr(test, derive(test_strategy::Arbitrary))]
pub enum NodeType {
    Leaf,
    Internal,
}

pub type Entry<K> = (K, Vec<u8>);
pub type EntryRef<'a, K> = (&'a K, &'a [u8]);

type LazyEntry<K> = (LazyKey<K>, LazyValue);

/// A node of a B-Tree.
///
/// There are two versions of a `Node`:
///
/// 1. `V1`, which supports only bounded types.
/// 2. `V2`, which supports both bounded and unbounded types.
///
/// See `v1.rs` and `v2.rs` for more details.
#[derive(Debug)]
pub struct Node<K: Storable + Ord + Clone> {
    address: Address,
    // List of tuples consisting of a key and the encoded value.
    // INVARIANT: the list is sorted by key.
    entries: Vec<LazyEntry<K>>,
    // For the key at position I, children[I] points to the left
    // child of this key and children[I + 1] points to the right child.
    children: Vec<Address>,
    node_type: NodeType,
    version: Version,

    // The address of the overflow page.
    // In V2, a node can span multiple pages if it exceeds a certain size.
    overflows: Vec<Address>,
}

impl<K: Storable + Ord + Clone> Node<K> {
    /// Loads a node from memory at the given address.
    pub fn load<M: Memory>(address: Address, page_size: PageSize, memory: &M) -> Self {
        // Load the header to determine which version the node is, then load the node accordingly.
        let header: NodeHeader = read_struct(address, memory);
        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        match header.version {
            LAYOUT_VERSION_1 => match page_size {
                PageSize::Derived(DerivedPageSize {
                    max_key_size,
                    max_value_size,
                }) => Self::load_v1(header, address, max_key_size, max_value_size, memory),
                PageSize::Value(_) => {
                    unreachable!("Tried to load a V1 node without a derived PageSize.")
                }
            },
            LAYOUT_VERSION_2 => Self::load_v2(address, page_size, header, memory),
            unknown_version => unreachable!("Unsupported version {unknown_version}."),
        }
    }

    /// Saves the node to memory.
    pub fn save<M: Memory>(&mut self, allocator: &mut Allocator<M>) {
        match self.version {
            Version::V1(_) => self.save_v1(allocator.memory()),
            Version::V2(_) => self.save_v2(allocator),
        }
    }

    /// Returns the address of the node.
    pub fn address(&self) -> Address {
        self.address
    }

    pub fn node_type(&self) -> NodeType {
        self.node_type
    }

    /// Returns the entry with the max key in the subtree.
    pub fn get_max<M: Memory>(&self, memory: &M) -> Entry<K> {
        match self.node_type {
            NodeType::Leaf => {
                let last_entry = self.entries.last().expect("A node can never be empty");
                (
                    self.get_key(last_entry, memory).clone(),
                    self.get_value(last_entry, memory).to_vec(),
                )
            }
            NodeType::Internal => {
                let last_child = Self::load(
                    *self
                        .children
                        .last()
                        .expect("An internal node must have children."),
                    self.version.page_size(),
                    memory,
                );
                last_child.get_max(memory)
            }
        }
    }

    /// Returns the entry with min key in the subtree.
    pub fn get_min<M: Memory>(&self, memory: &M) -> Entry<K> {
        match self.node_type {
            NodeType::Leaf => {
                // NOTE: a node can never be empty, so this access is safe.
                let entry = self.entry(0, memory);
                (entry.0.clone(), entry.1.to_vec())
            }
            NodeType::Internal => {
                let first_child = Self::load(
                    // NOTE: an internal node must have children, so this access is safe.
                    self.children[0],
                    self.version.page_size(),
                    memory,
                );
                first_child.get_min(memory)
            }
        }
    }

    /// Returns true if the node cannot store anymore entries, false otherwise.
    pub fn is_full(&self) -> bool {
        self.entries.len() >= CAPACITY
    }

    /// Replaces the value at `idx` and returns the old one.
    pub fn swap_value<M: Memory>(&mut self, idx: usize, new: Vec<u8>, memory: &M) -> Vec<u8> {
        let old = core::mem::replace(&mut self.entries[idx].1, LazyValue::by_value(new));
        self.extract_value(old, memory)
    }

    /// Swaps the entry at index `idx` with the given entry, returning the old entry.
    pub fn swap_entry<M: Memory>(
        &mut self,
        idx: usize,
        (key, value): Entry<K>,
        memory: &M,
    ) -> Entry<K> {
        let (old_key, old_value) = core::mem::replace(
            &mut self.entries[idx],
            (LazyKey::by_value(key), LazyValue::by_value(value)),
        );
        (
            self.extract_key(old_key, memory),
            self.extract_value(old_value, memory),
        )
    }

    /// Returns a reference to the entry at the specified index.
    #[inline(always)]
    pub fn entry<M: Memory>(&self, idx: usize, memory: &M) -> EntryRef<K> {
        (self.key(idx, memory), self.value(idx, memory))
    }

    #[inline(always)]
    fn get_key<'a, M: Memory>(&'a self, (k, _): &'a LazyEntry<K>, memory: &M) -> &'a K {
        k.get_or_load(|offset| self.load_key_from_memory(offset, memory))
    }

    /// Returns a reference to the cached value and loads it from memory if needed.
    #[inline(always)]
    fn get_value<'a, M: Memory>(&'a self, (_, v): &'a LazyEntry<K>, memory: &M) -> &'a [u8] {
        v.get_or_load(|offset| self.load_value_from_memory(offset, memory))
    }

    /// Returns a reference to the key at the specified index.
    #[inline(always)]
    pub fn key<M: Memory>(&self, idx: usize, memory: &M) -> &K {
        self.get_key(&self.entries[idx], memory)
    }

    /// Returns a reference to the encoded value at the specified index.
    #[inline(always)]
    pub fn value<M: Memory>(&self, idx: usize, memory: &M) -> &[u8] {
        self.get_value(&self.entries[idx], memory)
    }

    /// Extracts the contents of key (by loading it first if it's not loaded yet).
    fn extract_key<M: Memory>(&self, key: LazyKey<K>, memory: &M) -> K {
        key.take_or_load(|offset| self.load_key_from_memory(offset, memory))
    }

    /// Extracts the contents of value (by loading it first if it's not loaded yet).
    fn extract_value<M: Memory>(&self, value: LazyValue, memory: &M) -> Vec<u8> {
        value.take_or_load(|offset| self.load_value_from_memory(offset, memory))
    }

    /// Loads a key from stable memory at the given offset.
    fn load_key_from_memory<M: Memory>(&self, mut offset: Bytes, memory: &M) -> K {
        let reader = NodeReader {
            address: self.address,
            overflows: &self.overflows,
            page_size: self.page_size(),
            memory,
        };

        let size = match self.version {
            Version::V1(_) => {
                // V1: key size is always stored in memory.
                let size = read_u32(&reader, Address::from(offset.get()));
                offset += U32_SIZE;
                size
            }
            Version::V2(_) => {
                // V2: use fixed size if available, otherwise read from memory.
                if K::BOUND.is_fixed_size() {
                    K::BOUND.max_size()
                } else {
                    let size = read_u32(&reader, Address::from(offset.get()));
                    offset += U32_SIZE;
                    size
                }
            }
        } as usize;

        let mut bytes = Vec::with_capacity(size);
        read_to_vec(&reader, Address::from(offset.get()), &mut bytes, size);

        K::from_bytes(Cow::Borrowed(&bytes))
    }

    /// Loads a value from stable memory at the given offset.
    fn load_value_from_memory<M: Memory>(&self, offset: Bytes, memory: &M) -> Vec<u8> {
        let reader = NodeReader {
            address: self.address,
            overflows: &self.overflows,
            page_size: self.page_size(),
            memory,
        };

        let size = read_u32(&reader, Address::from(offset.get())) as usize;
        let mut bytes = Vec::with_capacity(size);
        read_to_vec(
            &reader,
            Address::from((offset + U32_SIZE).get()),
            &mut bytes,
            size,
        );

        bytes
    }

    fn page_size(&self) -> PageSize {
        self.version.page_size()
    }

    /// Returns the child's address at the given index.
    pub fn child(&self, idx: usize) -> Address {
        self.children[idx]
    }

    /// Inserts the given child at the given index.
    pub fn insert_child(&mut self, idx: usize, address: Address) {
        self.children.insert(idx, address)
    }

    /// Pushes the child to the far right of the node.
    pub fn push_child(&mut self, address: Address) {
        self.children.push(address)
    }

    /// Removes the child at the given index.
    pub fn remove_child(&mut self, idx: usize) -> Address {
        self.children.remove(idx)
    }

    /// Returns the number of children in the node.
    pub fn children_len(&self) -> usize {
        self.children.len()
    }

    /// Pops the right-most child of the node.
    pub fn pop_child(&mut self) -> Option<Address> {
        self.children.pop()
    }

    /// Inserts a new entry at the specified index.
    pub fn insert_entry(&mut self, idx: usize, (key, value): Entry<K>) {
        self.entries
            .insert(idx, (LazyKey::by_value(key), LazyValue::by_value(value)));
    }

    /// Returns the entry at the specified index while consuming this node.
    pub fn into_entry<M: Memory>(mut self, idx: usize, memory: &M) -> Entry<K> {
        let entries = core::mem::take(&mut self.entries);
        let (key, value) = entries.into_iter().nth(idx).unwrap();
        (
            self.extract_key(key, memory),
            self.extract_value(value, memory),
        )
    }

    /// Removes the entry at the specified index.
    pub fn remove_entry<M: Memory>(&mut self, idx: usize, memory: &M) -> Entry<K> {
        let (key, value) = self.entries.remove(idx);
        (
            self.extract_key(key, memory),
            self.extract_value(value, memory),
        )
    }

    /// Adds a new entry at the back of the node.
    pub fn push_entry(&mut self, (key, value): Entry<K>) {
        self.entries
            .push((LazyKey::by_value(key), LazyValue::by_value(value)));
    }

    /// Removes an entry from the back of the node.
    pub fn pop_entry<M: Memory>(&mut self, memory: &M) -> Option<Entry<K>> {
        let len = self.entries_len();
        if len == 0 {
            return None;
        }

        let (key, value) = self.entries.pop().expect("node must not be empty");

        Some((
            self.extract_key(key, memory),
            self.extract_value(value, memory),
        ))
    }

    /// Merges the entries and children of the `source` node into self, along with the median entry.
    ///
    /// PRECONDITION:
    ///   * `self` is not empty.
    ///   * `source` is not empty.
    ///   * `self` and `source` are of the same node type.
    ///
    /// POSTCONDITION:
    ///   * `source` is deallocated.
    ///   * all the entries of `source`, as well as the median, are merged into `self`, in sorted
    ///      order.
    pub fn merge<M: Memory>(
        &mut self,
        mut source: Node<K>,
        median: Entry<K>,
        allocator: &mut Allocator<M>,
    ) {
        // Load all the entries from the source node first, as they will be moved out.
        for i in 0..source.entries_len() {
            source.entry(i, allocator.memory());
        }

        if source.key(0, allocator.memory()) > self.key(0, allocator.memory()) {
            // The source node has keys that are greater than self.
            // Append the source node into self.
            Self::append(self, &mut source, median, allocator.memory());
        } else {
            // self has keys that are greater than the source node.
            // Append self into the source node (which more efficient).
            Self::append(&mut source, self, median, allocator.memory());

            // Move the entries and children into self.
            self.entries = core::mem::take(&mut source.entries);
            self.children = core::mem::take(&mut source.children);
        }

        self.save(allocator);
        source.deallocate(allocator);
    }

    /// Appends the entries and children of node `b` into `a`, along with the median entry.
    ///
    /// PRECONDITION:
    ///   * `a` is not empty.
    ///   * `b` is not empty.
    ///   * `a` and `b` are of the same node type.
    ///   * keys of `a` < median < keys of `b`
    ///
    /// POSTCONDITION:
    ///   * `b` is empty.
    fn append<M: Memory>(a: &mut Node<K>, b: &mut Node<K>, median: Entry<K>, memory: &M) {
        // Assert preconditions.
        let a_len = a.entries_len();
        assert_eq!(a.node_type(), b.node_type());
        assert!(b.entries_len() > 0);
        assert!(a_len > 0);
        assert!(a.key(a_len - 1, memory) < &median.0);
        assert!(&median.0 < b.key(0, memory));

        a.push_entry(median);

        a.entries.append(&mut b.entries);

        // Move the children (if any exist).
        a.children.append(&mut b.children);

        // Assert postconditions.
        assert_eq!(b.entries.len(), 0);
        assert_eq!(b.children.len(), 0);
    }

    #[cfg(test)]
    pub fn entries<M: Memory>(&self, memory: &M) -> Vec<Entry<K>> {
        (0..self.entries.len())
            .map(|i| (self.key(i, memory).clone(), self.value(i, memory).to_vec()))
            .collect()
    }

    #[cfg(test)]
    pub fn keys<M: Memory>(&self, memory: &M) -> Vec<&K> {
        (0..self.entries.len())
            .map(|i| self.key(i, memory))
            .collect()
    }

    #[cfg(test)]
    pub fn overflows(&self) -> &[Address] {
        &self.overflows
    }

    /// Returns the number of entries in the node.
    pub fn entries_len(&self) -> usize {
        self.entries.len()
    }

    /// Searches for the key in the node's entries.
    ///
    /// If the key is found then `Result::Ok` is returned, containing the index
    /// of the matching key. If the value is not found then `Result::Err` is
    /// returned, containing the index where a matching key could be inserted
    /// while maintaining sorted order.
    pub fn search<M: Memory>(&self, key: &K, memory: &M) -> Result<usize, usize> {
        self.entries
            .binary_search_by_key(&key, |entry| self.get_key(entry, memory))
    }

    /// Returns the maximum size a node can be if it has bounded keys and values.
    ///
    /// See the documentation of [`Node`] for the memory layout.
    pub fn max_size(max_key_size: u32, max_value_size: u32) -> Bytes {
        v1::size_v1(max_key_size, max_value_size)
    }

    /// Returns true if the node is at the minimum required size, false otherwise.
    pub fn at_minimum(&self) -> bool {
        self.entries.len() < B
    }

    /// Returns true if an entry can be removed without having to merge it into another node
    /// (i.e. without going below the minimum size of a node).
    pub fn can_remove_entry_without_merging(&self) -> bool {
        !self.at_minimum()
    }

    /// Moves elements from own node to a sibling node and returns the median element.
    pub fn split<M: Memory>(&mut self, sibling: &mut Node<K>, memory: &M) -> Entry<K> {
        debug_assert!(self.is_full());

        // Load the entries that will be moved out of the node and into the new sibling.
        for idx in B..self.entries_len() {
            self.entry(idx, memory);
        }

        // Move the entries and children above the median into the new sibling.
        sibling.entries = self.entries.split_off(B);
        if self.node_type == NodeType::Internal {
            sibling.children = self.children.split_off(B);
        }

        // Return the median entry.
        self.pop_entry(memory)
            .expect("An initially full node cannot be empty")
    }

    /// Deallocates a node.
    pub fn deallocate<M: Memory>(self, allocator: &mut Allocator<M>) {
        for overflow in self.overflows.into_iter() {
            allocator.deallocate(overflow);
        }

        allocator.deallocate(self.address);
    }
}

// A transient data structure for reading/writing metadata into/from stable memory.
#[repr(C, packed)]
struct NodeHeader {
    magic: [u8; 3],
    version: u8,
    node_type: u8,
    num_entries: u16,
}

impl NodeHeader {
    fn size() -> Bytes {
        Bytes::from(core::mem::size_of::<Self>() as u64)
    }
}

/// A lazily-loaded object, which can be either an immediate value or a deferred reference.
#[derive(Debug)]
enum LazyObject<T> {
    ByVal(T),
    ByRef { offset: Bytes, loaded: OnceCell<T> },
}

impl<T> LazyObject<T> {
    #[inline(always)]
    pub fn by_value(value: T) -> Self {
        LazyObject::ByVal(value)
    }

    #[inline(always)]
    pub fn by_ref(offset: Bytes) -> Self {
        LazyObject::ByRef {
            offset,
            loaded: OnceCell::new(),
        }
    }

    #[inline(always)]
    pub fn get_or_load(&self, load: impl FnOnce(Bytes) -> T) -> &T {
        match self {
            LazyObject::ByVal(value) => value,
            LazyObject::ByRef { offset, loaded } => loaded.get_or_init(|| load(*offset)),
        }
    }

    #[inline(always)]
    pub fn take_or_load(self, load: impl FnOnce(Bytes) -> T) -> T {
        match self {
            LazyObject::ByVal(value) => value,
            LazyObject::ByRef { offset, loaded } => {
                loaded.into_inner().unwrap_or_else(|| load(offset))
            }
        }
    }
}

type Blob = Vec<u8>;

#[derive(Debug)]
struct LazyValue(LazyObject<Blob>);

impl LazyValue {
    #[inline(always)]
    pub fn by_value(value: Blob) -> Self {
        Self(LazyObject::by_value(value))
    }

    #[inline(always)]
    pub fn by_ref(offset: Bytes) -> Self {
        Self(LazyObject::by_ref(offset))
    }

    #[inline(always)]
    pub fn get_or_load(&self, load: impl FnOnce(Bytes) -> Blob) -> &Blob {
        self.0.get_or_load(load)
    }

    #[inline(always)]
    pub fn take_or_load(self, load: impl FnOnce(Bytes) -> Blob) -> Blob {
        self.0.take_or_load(load)
    }
}

#[derive(Debug)]
struct LazyKey<K>(LazyObject<K>);

impl<K> LazyKey<K> {
    #[inline(always)]
    pub fn by_value(value: K) -> Self {
        Self(LazyObject::by_value(value))
    }

    #[inline(always)]
    pub fn by_ref(offset: Bytes) -> Self {
        Self(LazyObject::by_ref(offset))
    }

    #[inline(always)]
    pub fn get_or_load(&self, load: impl FnOnce(Bytes) -> K) -> &K {
        self.0.get_or_load(load)
    }

    #[inline(always)]
    pub fn take_or_load(self, load: impl FnOnce(Bytes) -> K) -> K {
        self.0.take_or_load(load)
    }
}

/// Stores version-specific data.
#[derive(Debug, PartialEq, Copy, Clone, Eq)]
pub enum Version {
    /// V1 nodes have a page size derived from the max key/value sizes.
    V1(DerivedPageSize),
    /// V2 nodes have a fixed page size.
    V2(PageSize),
}

impl Version {
    pub fn page_size(&self) -> PageSize {
        match self {
            Self::V1(page_size) => PageSize::Derived(*page_size),
            Self::V2(page_size) => *page_size,
        }
    }
}

/// The size of an individual page in the memory where nodes are stored.
/// A node, if it's bigger than a single page, overflows into multiple pages.
#[allow(dead_code)]
#[derive(Debug, PartialEq, Copy, Clone, Eq)]
pub enum PageSize {
    /// Derived page sizes are used when migrating nodes from v1 to v2.
    /// A migration from v1 nodes to v2 is done incrementally. Children of a v2 node
    /// may be a v1 node, and storing the maximum sizes around is necessary to be able
    /// to load v1 nodes.
    Derived(DerivedPageSize),
    Value(u32),
}

impl PageSize {
    pub fn get(&self) -> u32 {
        match self {
            Self::Value(page_size) => *page_size,
            Self::Derived(page_size) => page_size.get(),
        }
    }
}

/// A page size derived from the maximum sizes of the keys and values.
#[derive(Debug, PartialEq, Copy, Clone, Eq)]
pub struct DerivedPageSize {
    pub max_key_size: u32,
    pub max_value_size: u32,
}

impl DerivedPageSize {
    /// Returns the page size derived from the max key/value sizes.
    fn get(&self) -> u32 {
        v1::size_v1(self.max_key_size, self.max_value_size).get() as u32
    }
}
