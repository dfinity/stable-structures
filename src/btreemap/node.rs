use crate::{
    read_struct, read_u16, read_u32, read_u64,
    storable::Storable,
    types::{Address, Bytes},
    write, write_struct, write_u16, write_u32, Memory,
};
use std::borrow::{Borrow, Cow};
use std::cell::{Cell, Ref, RefCell};

#[cfg(test)]
mod tests;
mod v1;
mod v2;

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
const NODE_HEADER_SIZE: Bytes = Bytes::new(7);

#[derive(Debug, PartialEq, Copy, Clone, Eq)]
pub enum NodeType {
    Leaf,
    Internal,
}

pub type Entry<K> = (K, Vec<u8>);

#[derive(Debug, PartialEq, Copy, Clone, Eq)]
pub enum Version {
    V1,
    V2,
}

/// A node of a B-Tree.
///
/// Depending on the layout version, the node can be represented differently in stable memory.
/// The default layout version is V2. You can read more about the different layouts in `v1.rs`
/// and `v2.rs`.
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
    max_key_size: u32,
    max_value_size: u32,

    // The node's layout version. Stored in a cell to allow bumping the version without
    // requiring exterior mutability.
    version: Cell<Version>,
}

impl<K: Storable + Ord + Clone> Node<K> {
    /// Creates a new node at the given address.
    pub fn new(
        address: Address,
        node_type: NodeType,
        max_key_size: u32,
        max_value_size: u32,
    ) -> Node<K> {
        Node {
            address,
            keys: vec![],
            encoded_values: RefCell::default(),
            children: vec![],
            node_type,
            max_key_size,
            max_value_size,
            version: get_version_to_use(max_key_size).into(),
        }
    }

    /// Loads a node from memory at the given address.
    pub fn load<M: Memory>(
        address: Address,
        memory: &M,
        max_key_size: u32,
        max_value_size: u32,
    ) -> Self {
        // Load the header.
        let header: NodeHeader = read_struct(address, memory);
        assert_eq!(&header.magic, MAGIC, "Bad magic.");

        match header.version {
            LAYOUT_VERSION_1 => {
                Self::load_v1(address, header, memory, max_key_size, max_value_size)
            }
            LAYOUT_VERSION_2 => {
                Self::load_v2(address, header, memory, max_key_size, max_value_size)
            }
            _ => panic!("Unsupported node version."),
        }
    }

    /// Saves the node to memory.
    pub fn save<M: Memory>(&self, memory: &M) {
        match self.node_type {
            NodeType::Leaf => {
                assert!(self.children.is_empty());
            }
            NodeType::Internal => {
                assert_eq!(self.children.len(), self.keys.len() + 1);
            }
        };

        // We should never be saving an empty node.
        assert!(!self.keys.is_empty() || !self.children.is_empty());

        // Assert entries are sorted in strictly increasing order.
        assert!(self.keys.windows(2).all(|e| e[0] < e[1]));

        // When possible, nodes are migrated to version 2 as it's more performant.
        match get_version_to_use(self.max_key_size) {
            Version::V1 => self.save_v1(memory),
            Version::V2 => self.save_v2(memory),
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
                    self.max_key_size,
                    self.max_value_size,
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
                    self.max_key_size,
                    self.max_value_size,
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
                let value_address = self.value_address(offset);
                let value_len = read_u32(memory, value_address) as usize;
                let mut value = vec![0; value_len];
                memory.read((value_address + U32_SIZE).get(), &mut value);

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

    // Returns the address of the value at the given index.
    fn value_address(&self, idx: u8) -> Address {
        self.address
            + match self.version.get() {
                Version::V1 => self.value_offset_v1(idx),
                Version::V2 => self.value_offset_v2(idx),
            }
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

    #[allow(dead_code)]
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
        // The size of both layouts are the same.
        let size = Self::size_v2(max_key_size, max_value_size);
        debug_assert_eq!(size, Self::size_v1(max_key_size, max_value_size));
        size
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
    const fn size() -> Bytes {
        NODE_HEADER_SIZE
    }
}

// The value in a K/V pair.
#[derive(Debug)]
enum Value {
    // The value's encoded bytes.
    ByVal(Vec<u8>),

    // The value's index in the node.
    ByRef(u8),
}

// Determines which node layout version to use.
fn get_version_to_use(max_key_size: u32) -> Version {
    if max_key_size > u16::MAX as u32 {
        Version::V1
    } else {
        Version::V2
    }
}

#[test]
fn node_header_size_is_correct() {
    assert_eq!(
        core::mem::size_of::<NodeHeader>(),
        NODE_HEADER_SIZE.get() as usize
    );
}
