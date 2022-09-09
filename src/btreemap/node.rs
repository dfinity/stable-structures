use crate::{
    read_struct, read_u32, read_u64,
    types::{Address, Bytes},
    write, write_struct, write_u32, Memory,
};

/// The minimum degree to use in the btree.
/// This constant is taken from Rust's std implementation of BTreeMap.
pub const B: u64 = 6;
/// The maximum number of entries per node.
pub const CAPACITY: u64 = 2 * B - 1;
const LAYOUT_VERSION: u8 = 1;
const MAGIC: &[u8; 3] = b"BTN";
const LEAF_NODE_TYPE: u8 = 0;
const INTERNAL_NODE_TYPE: u8 = 1;
// The size of u32 in bytes.
const U32_SIZE: Bytes = Bytes::new(4);

// Entries in the node are key-value pairs and both are blobs.
pub type Entry = (Vec<u8>, Vec<u8>);

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum NodeType {
    Leaf,
    Internal,
}

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
#[derive(Debug, PartialEq)]
pub struct Node {
    pub address: Address,
    pub entries: Vec<Entry>,
    pub children: Vec<Address>,
    pub node_type: NodeType,
    pub max_key_size: u32,
    pub max_value_size: u32,
}

impl Node {
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
        let mut entries = vec![];
        let mut offset = NodeHeader::size();
        for _ in 0..header.num_entries {
            // Read the key's size.
            let key_size = read_u32(memory, address + offset);
            offset += U32_SIZE;

            // Read the key.
            let mut key = vec![0; key_size as usize];
            memory.read((address + offset).get(), &mut key);
            offset += Bytes::from(max_key_size as u64);

            // Read the value's size.
            let value_size = read_u32(memory, address + offset);
            offset += U32_SIZE;

            // Read the value.
            let mut value = vec![0; value_size as usize];
            memory.read((address + offset).get(), &mut value);
            offset += Bytes::from(max_value_size as u64);

            entries.push((key, value));
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

            assert_eq!(children.len(), entries.len() + 1);
        }

        Self {
            address,
            entries,
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
                assert_eq!(self.children.len(), self.entries.len() + 1);
            }
        };

        // We should never be saving an empty node.
        assert!(!self.entries.is_empty() || !self.children.is_empty());

        // Assert entries are sorted in strictly increasing order.
        assert!(self.entries.windows(2).all(|e| e[0].0 < e[1].0));

        let header = NodeHeader {
            magic: *MAGIC,
            version: LAYOUT_VERSION,
            node_type: match self.node_type {
                NodeType::Leaf => LEAF_NODE_TYPE,
                NodeType::Internal => INTERNAL_NODE_TYPE,
            },
            num_entries: self.entries.len() as u16,
        };

        write_struct(&header, self.address, memory);

        let mut offset = NodeHeader::size();

        // Write the entries.
        for (key, value) in self.entries.iter() {
            // Write the size of the key.
            write_u32(memory, self.address + offset, key.len() as u32);
            offset += U32_SIZE;

            // Write the key.
            write(memory, (self.address + offset).get(), key);
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

    /// Returns the entry with the max key in the subtree.
    pub fn get_max<M: Memory>(&self, memory: &M) -> Entry {
        match self.node_type {
            NodeType::Leaf => self
                .entries
                .last()
                .expect("A node can never be empty")
                .clone(),
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
    pub fn get_min(&self, memory: &impl Memory) -> Entry {
        match self.node_type {
            NodeType::Leaf => {
                // NOTE: a node can never be empty, so this access is safe.
                self.entries[0].clone()
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
        self.entries.len() >= CAPACITY as usize
    }

    /// Swaps the entry at index `idx` with the given entry, returning the old entry.
    pub fn swap_entry(&mut self, idx: usize, mut entry: Entry) -> Entry {
        core::mem::swap(&mut self.entries[idx], &mut entry);
        entry
    }

    /// Searches for the key in the node's entries.
    ///
    /// If the key is found then `Result::Ok` is returned, containing the index
    /// of the matching key. If the value is not found then `Result::Err` is
    /// returned, containing the index where a matching key could be inserted
    /// while maintaining sorted order.
    pub fn get_key_idx(&mut self, key: &[u8]) -> Result<usize, usize> {
        self.entries.binary_search_by(|e| e.0.as_slice().cmp(key))
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
            + Bytes::from(CAPACITY) * entry_size
            + Bytes::from(CAPACITY + 1) * child_size
    }
}

// A transient data structure for reading/writing metadata into/from stable memory.
#[repr(packed)]
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
