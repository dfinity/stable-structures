use crate::{
    read_struct, read_u32, read_u64,
    storable::Storable,
    types::{Address, Bytes},
    write, write_struct, write_u32, Memory,
};
use std::borrow::{Borrow, Cow};

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
pub enum NodeType {
    Leaf,
    Internal,
}

pub type Entry<K> = (K, Vec<u8>);

/// A node of a B-Tree.
///
/// The node is stored in stable memory with the following layout:
///
///    |  NodeHeader  |  Entries (keys and values) |  Children  |
///
/// Each node contains up to `CAPACITY` entries, each entry contains:
///     - size of key (4 bytes)
///     - key (`max_key_size` bytes)
///     - size of value (4 bytes)
///     - value (`max_value_size` bytes)
///
/// Each node can contain up to `CAPACITY + 1` children, each child is 8 bytes.
#[derive(Debug, PartialEq, Eq)]
pub struct Node<K: Storable + Ord + Clone> {
    pub address: Address,
    pub keys: Vec<K>,
    pub encoded_values: Vec<Vec<u8>>,
    /// For the key at position I, children[I] points to the left
    /// child of this key and children[I + 1] points to the right child.
    pub children: Vec<Address>,
    pub node_type: NodeType,
    max_key_size: u32,
    max_value_size: u32,
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
            encoded_values: vec![],
            children: vec![],
            node_type,
            max_key_size,
            max_value_size,
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
        assert_eq!(header.version, LAYOUT_VERSION, "Unsupported version.");

        // Load the entries.
        let mut keys = Vec::with_capacity(header.num_entries as usize);
        let mut encoded_values = Vec::with_capacity(header.num_entries as usize);
        let mut offset = NodeHeader::size();
        let mut buf = Vec::with_capacity(max_key_size.max(max_value_size) as usize);
        for _ in 0..header.num_entries {
            // Read the key's size.
            let key_size = read_u32(memory, address + offset);
            offset += U32_SIZE;

            // Read the key.
            buf.resize(key_size as usize, 0);
            memory.read((address + offset).get(), &mut buf);
            offset += Bytes::from(max_key_size as u64);
            let key = K::from_bytes(Cow::Borrowed(&buf));

            // Read the value's size.
            let value_size = read_u32(memory, address + offset);
            offset += U32_SIZE;

            // Read the value.
            let mut value = vec![0; value_size as usize];
            memory.read((address + offset).get(), &mut value);
            offset += Bytes::from(max_value_size as u64);

            keys.push(key);
            encoded_values.push(value);
        }

        // Load children if this is an internal node.
        let mut children = vec![];
        if header.node_type == INTERNAL_NODE_TYPE {
            // The number of children is equal to the number of entries + 1.
            for _ in 0..header.num_entries + 1 {
                let child = Address::from(read_u64(memory, address + offset));
                offset += Address::size();
                children.push(child);
            }

            assert_eq!(children.len(), keys.len() + 1);
        }

        Self {
            address,
            keys,
            encoded_values,
            children,
            node_type: match header.node_type {
                LEAF_NODE_TYPE => NodeType::Leaf,
                INTERNAL_NODE_TYPE => NodeType::Internal,
                other => unreachable!("Unknown node type {}", other),
            },
            max_key_size,
            max_value_size,
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

        let header = NodeHeader {
            magic: *MAGIC,
            version: LAYOUT_VERSION,
            node_type: match self.node_type {
                NodeType::Leaf => LEAF_NODE_TYPE,
                NodeType::Internal => INTERNAL_NODE_TYPE,
            },
            num_entries: self.keys.len() as u16,
        };

        write_struct(&header, self.address, memory);

        let mut offset = NodeHeader::size();

        // Write the entries.
        for (key, value) in self.iter_entries() {
            // Write the size of the key.
            let key_bytes = key.to_bytes();
            write_u32(memory, self.address + offset, key_bytes.len() as u32);
            offset += U32_SIZE;

            // Write the key.
            write(memory, (self.address + offset).get(), key_bytes.borrow());
            offset += Bytes::from(self.max_key_size);

            // Write the size of the value.
            write_u32(memory, self.address + offset, value.len() as u32);
            offset += U32_SIZE;

            // Write the value.
            write(memory, (self.address + offset).get(), value);
            offset += Bytes::from(self.max_value_size);
        }

        // Write the children
        for child in self.children.iter() {
            write(
                memory,
                (self.address + offset).get(),
                &child.get().to_le_bytes(),
            );
            offset += Address::size();
        }
    }

    pub fn iter_entries(&self) -> impl Iterator<Item = (&K, &[u8])> {
        self.keys
            .iter()
            .zip(self.encoded_values.iter().map(|v| &v[..]))
    }

    /// Returns the entry with the max key in the subtree.
    pub fn get_max<M: Memory>(&self, memory: &M) -> Entry<K> {
        match self.node_type {
            NodeType::Leaf => (
                self.keys.last().expect("A node can never be empty").clone(),
                self.encoded_values.last().unwrap().clone(),
            ),
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
    pub fn get_min(&self, memory: &impl Memory) -> Entry<K> {
        match self.node_type {
            NodeType::Leaf => {
                // NOTE: a node can never be empty, so this access is safe.
                self.entry(0)
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
    pub fn swap_entry(&mut self, idx: usize, mut entry: Entry<K>) -> Entry<K> {
        core::mem::swap(&mut self.keys[idx], &mut entry.0);
        core::mem::swap(&mut self.encoded_values[idx], &mut entry.1);
        entry
    }

    /// Returns a copy of the entry at the specified index.
    pub fn entry(&self, idx: usize) -> Entry<K> {
        (self.keys[idx].clone(), self.encoded_values[idx].clone())
    }

    /// Inserts a new entry at the specified index.
    pub fn insert_entry(&mut self, idx: usize, (key, encoded_value): Entry<K>) {
        self.keys.insert(idx, key);
        self.encoded_values.insert(idx, encoded_value);
    }

    /// Removes the entry at the specified index.
    pub fn remove_entry(&mut self, idx: usize) -> Entry<K> {
        (self.keys.remove(idx), self.encoded_values.remove(idx))
    }

    /// Adds a new entry at the back of the node.
    pub fn push_entry(&mut self, (key, encoded_value): Entry<K>) {
        self.keys.push(key);
        self.encoded_values.push(encoded_value);
    }

    /// Removes an entry from the back of the node.
    pub fn pop_entry(&mut self) -> Option<Entry<K>> {
        let key = self.keys.pop()?;
        let val = self.encoded_values.pop()?;
        Some((key, val))
    }

    /// Moves entries from the `other` node to the back of this node.
    pub fn append_entries_from(&mut self, other: &mut Node<K>) {
        self.keys.append(&mut other.keys);
        self.encoded_values.append(&mut other.encoded_values);
    }

    #[allow(dead_code)]
    pub fn entries(&self) -> Vec<Entry<K>> {
        self.iter_entries()
            .map(|(k, v)| (k.clone(), v.to_vec()))
            .collect()
    }

    /// Searches for the key in the node's entries.
    ///
    /// If the key is found then `Result::Ok` is returned, containing the index
    /// of the matching key. If the value is not found then `Result::Err` is
    /// returned, containing the index where a matching key could be inserted
    /// while maintaining sorted order.
    pub fn get_key_idx(&mut self, key: &K) -> Result<usize, usize> {
        self.keys.binary_search(key)
    }

    /// Returns the size of a node in bytes.
    ///
    /// See the documentation of [`Node`] for the memory layout.
    pub fn size(max_key_size: u32, max_value_size: u32) -> Bytes {
        let max_key_size = Bytes::from(max_key_size);
        let max_value_size = Bytes::from(max_value_size);

        let node_header_size = NodeHeader::size();
        let entry_size = U32_SIZE + max_key_size + max_value_size + U32_SIZE;
        let child_size = Address::size();

        node_header_size
            + Bytes::from(CAPACITY as u64) * entry_size
            + Bytes::from((CAPACITY + 1) as u64) * child_size
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
    pub fn split(&mut self, sibling: &mut Node<K>) -> Entry<K> {
        debug_assert!(self.is_full());

        // Move the entries and children above the median into the new sibling.
        sibling.keys = self.keys.split_off(B);
        sibling.encoded_values = self.encoded_values.split_off(B);
        if self.node_type == NodeType::Internal {
            sibling.children = self.children.split_off(B);
        }

        // Return the median entry.
        self.pop_entry()
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
