use crate::{
    btreemap::Allocator,
    read_struct, read_u32, read_u64,
    storable::Storable,
    types::{Address, Bytes},
    write, write_struct, write_u32, Memory,
};
use std::borrow::{Borrow, Cow};
use std::cell::{Ref, RefCell};

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
const LAYOUT_VERSION: u8 = 1;
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
    keys: Vec<K>,
    // Values are stored in a Refcell as they are loaded lazily.
    // A RefCell allows loading the value and caching it without requiring exterior mutability.
    encoded_values: RefCell<Vec<Value>>,
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
    pub fn load<M: Memory>(address: Address, memory: &M, version: Version) -> Self {
        match version {
            Version::V1(DerivedPageSize {
                max_key_size,
                max_value_size,
            }) => Self::load_v1(address, max_key_size, max_value_size, memory),
            Version::V2(page_size) => Self::load_v2(address, page_size, memory),
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
                let last_idx = self.encoded_values.borrow().len() - 1;
                (
                    self.keys.last().expect("A node can never be empty").clone(),
                    self.value(last_idx, memory).to_vec(),
                )
            }
            NodeType::Internal => {
                let last_child = Self::load(
                    *self
                        .children
                        .last()
                        .expect("An internal node must have children."),
                    memory,
                    self.version,
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
                self.entry(0, memory)
            }
            NodeType::Internal => {
                let first_child = Self::load(
                    // NOTE: an internal node must have children, so this access is safe.
                    self.children[0],
                    memory,
                    self.version,
                );
                first_child.get_min(memory)
            }
        }
    }

    /// Returns true if the node cannot store anymore entries, false otherwise.
    pub fn is_full(&self) -> bool {
        self.keys.len() >= CAPACITY
    }

    /// Swaps the entry at index `idx` with the given entry, returning the old entry.
    pub fn swap_entry<M: Memory>(
        &mut self,
        idx: usize,
        (mut key, value): Entry<K>,
        memory: &M,
    ) -> Entry<K> {
        core::mem::swap(&mut self.keys[idx], &mut key);
        let old_value = self.value(idx, memory).to_vec();
        self.encoded_values.borrow_mut()[idx] = Value::ByVal(value);
        (key, old_value)
    }

    /// Returns a copy of the entry at the specified index.
    pub fn entry<M: Memory>(&self, idx: usize, memory: &M) -> Entry<K> {
        (self.keys[idx].clone(), self.value(idx, memory).to_vec())
    }

    /// Returns a reference to the encoded value at the specified index.
    pub fn value<M: Memory>(&self, idx: usize, memory: &M) -> Ref<[u8]> {
        // Load and cache the value from the underlying memory if needed.
        {
            let mut values = self.encoded_values.borrow_mut();

            if let Value::ByRef(offset) = values[idx] {
                // Value isn't loaded yet.
                let reader = NodeReader {
                    address: self.address,
                    overflows: &self.overflows,
                    page_size: self.page_size(),
                    memory,
                };

                let value_len = read_u32(&reader, Address::from(offset.get())) as usize;
                let mut value = vec![0; value_len];
                reader.read((offset + U32_SIZE).get(), &mut value);

                // Cache the value internally.
                values[idx] = Value::ByVal(value);
            }
        }

        // Return a reference to the value.
        Ref::map(self.encoded_values.borrow(), |values| {
            if let Value::ByVal(v) = &values[idx] {
                &v[..]
            } else {
                unreachable!("value must have been loaded already.");
            }
        })
    }

    fn page_size(&self) -> PageSize {
        self.version.page_size()
    }

    /// Returns a reference to the key at the specified index.
    pub fn key(&self, idx: usize) -> &K {
        &self.keys[idx]
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
    pub fn insert_entry(&mut self, idx: usize, (key, encoded_value): Entry<K>) {
        self.keys.insert(idx, key);
        self.encoded_values
            .borrow_mut()
            .insert(idx, Value::ByVal(encoded_value));
    }

    /// Removes the entry at the specified index.
    pub fn remove_entry<M: Memory>(&mut self, idx: usize, memory: &M) -> Entry<K> {
        let value = self.value(idx, memory).to_vec();
        self.encoded_values.borrow_mut().remove(idx);
        (self.keys.remove(idx), value)
    }

    /// Adds a new entry at the back of the node.
    pub fn push_entry(&mut self, (key, encoded_value): Entry<K>) {
        self.keys.push(key);
        self.encoded_values
            .borrow_mut()
            .push(Value::ByVal(encoded_value));
    }

    /// Removes an entry from the back of the node.
    pub fn pop_entry<M: Memory>(&mut self, memory: &M) -> Option<Entry<K>> {
        let len = self.entries_len();
        if len == 0 {
            return None;
        }

        let key = self.keys.pop().expect("node must not be empty");
        let last_value = self.value(len - 1, memory).to_vec();
        self.encoded_values
            .borrow_mut()
            .pop()
            .expect("node must not be empty");

        Some((key, last_value))
    }

    /// Merges the entries and children of the `source` node into self, along with the median entry.
    ///
    /// PRECONDITION:
    ///   * `self` is not empty.
    ///   * `source` is not empty.
    ///   * `self` and `source` are of the same node type.
    ///
    /// POSTCONDITION:
    ///   * `source` is empty (no entries and no children).
    ///   * all the entries of `source`, as well as the median, are merged into `self`, in sorted
    ///      order.
    pub fn merge<M: Memory>(&mut self, mut source: Node<K>, median: Entry<K>, memory: &M) {
        // Load all the values from the source node first, as they will be moved out.
        for i in 0..source.entries_len() {
            source.value(i, memory);
        }

        if source.key(0) > self.key(0) {
            // The source node has keys that are greater than self.
            // Append the source node into self.
            Self::append(self, &mut source, median);
        } else {
            // self has keys that are greater than the source node.
            // Append self into the source node (which more efficient).
            Self::append(&mut source, self, median);

            // Move the entries and children into self.
            self.keys = source.keys;
            self.encoded_values = source.encoded_values;
            self.children = source.children;
        }
    }

    // Appends the entries and children of node `b` into `a`, along with the median entry.
    //
    // PRECONDITION:
    //   * `a` is not empty.
    //   * `b` is not empty.
    //   * `a` and `b` are of the same node type.
    //   * keys of `a` < median < keys of `b`
    //
    // POSTCONDITION:
    //   * `b` is empty.
    fn append(a: &mut Node<K>, b: &mut Node<K>, median: Entry<K>) {
        // Assert preconditions.
        let a_len = a.entries_len();
        assert_eq!(a.node_type(), b.node_type());
        assert!(b.entries_len() > 0);
        assert!(a_len > 0);
        assert!(a.key(a_len - 1) < &median.0);
        assert!(&median.0 < b.key(0));

        a.push_entry(median);

        a.keys.append(&mut b.keys);
        a.encoded_values
            .borrow_mut()
            .append(&mut b.encoded_values.borrow_mut());

        // Move the children (if any exist).
        a.children.append(&mut b.children);

        // Assert postconditions.
        assert_eq!(b.keys.len(), 0);
        assert_eq!(b.encoded_values.borrow().len(), 0);
        assert_eq!(b.children.len(), 0);
    }

    #[cfg(test)]
    pub fn entries<M: Memory>(&self, memory: &M) -> Vec<Entry<K>> {
        self.keys
            .iter()
            .cloned()
            .zip((0..self.keys.len()).map(|idx| self.value(idx, memory).to_vec()))
            .collect()
    }

    /// Returns the number of entries in the node.
    pub fn entries_len(&self) -> usize {
        self.keys.len()
    }

    /// Searches for the key in the node's entries.
    ///
    /// If the key is found then `Result::Ok` is returned, containing the index
    /// of the matching key. If the value is not found then `Result::Err` is
    /// returned, containing the index where a matching key could be inserted
    /// while maintaining sorted order.
    pub fn search(&self, key: &K) -> Result<usize, usize> {
        self.keys.binary_search(key)
    }

    /// Returns the size of a node in bytes.
    ///
    /// See the documentation of [`Node`] for the memory layout.
    pub fn size(max_key_size: u32, max_value_size: u32) -> Bytes {
        v1::size_v1(max_key_size, max_value_size)
    }

    /// Returns true if the node is at the minimum required size, false otherwise.
    pub fn at_minimum(&self) -> bool {
        self.keys.len() < B
    }

    /// Returns true if an entry can be removed without having to merge it into another node
    /// (i.e. without going below the minimum size of a node).
    pub fn can_remove_entry_without_merging(&self) -> bool {
        !self.at_minimum()
    }

    /// Moves elements from own node to a sibling node and returns the median element.
    pub fn split<M: Memory>(&mut self, sibling: &mut Node<K>, memory: &M) -> Entry<K> {
        debug_assert!(self.is_full());

        // Load the values that will be moved out of the node and into the new sibling.
        for idx in B..self.entries_len() {
            self.value(idx, memory);
        }

        // Move the entries and children above the median into the new sibling.
        sibling.keys = self.keys.split_off(B);
        *sibling.encoded_values.borrow_mut() = self.encoded_values.borrow_mut().split_off(B);
        if self.node_type == NodeType::Internal {
            sibling.children = self.children.split_off(B);
        }

        // Return the median entry.
        self.pop_entry(memory)
            .expect("An initially full node cannot be empty")
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

// The value in a K/V pair.
#[derive(Debug)]
enum Value {
    // The value's encoded bytes.
    ByVal(Vec<u8>),

    // The value's offset in the node.
    ByRef(Bytes),
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
    // Returns the page size derived from the max key/value sizes.
    fn get(&self) -> u32 {
        v1::size_v1(self.max_key_size, self.max_value_size).get() as u32
    }
}
