//! Node V1
//!
//! A v1 node is the first node layout, with fixed node sizes and support for
//! bounded types only.
//!
//! # Memory Layout
//!
//! ```text
//! ---------------------------------------- <-- Header
//! Magic "BTN"             ↕ 3 bytes
//! ----------------------------------------
//! Layout version (2)      ↕ 1 byte
//! ----------------------------------------
//! Node type               ↕ 1 byte
//! ----------------------------------------
//! # Entries (k)           ↕ 2 bytes
//! ---------------------------------------- <-- Entries (up to `CAPACITY` entries)
//! Key(0) size             ↕ 4 bytes
//! ----------------------------------------
//! Key(0)                  ↕ `max_key_size` bytes
//! ----------------------------------------
//! Value(0) size           ↕ 4 bytes
//! ----------------------------------------
//! Value(0)                ↕ `max_value_size` bytes
//! ----------------------------------------
//! Key(1) size             ↕ 4 bytes
//! ----------------------------------------
//! Key(1)                  ↕ `max_key_size` bytes
//! ----------------------------------------
//! Value(1) size           ↕ 4 bytes
//! ----------------------------------------
//! Value(1)                ↕ `max_value_size` bytes
//! ----------------------------------------
//! ...
//! ---------------------------------------- <-- Children (up to `CAPACITY + 1` children)
//! Child(0) address        ↕ 8 bytes
//! ----------------------------------------
//! ...
//! ----------------------------------------
//! Child(k + 1) address    ↕ 8 bytes
//! ----------------------------------------
//! ```
use super::*;

impl<K: Storable + Ord + Clone> Node<K> {
    /// Creates a new v1 node at the given address.
    pub fn new_v1(address: Address, node_type: NodeType, page_size: DerivedPageSize) -> Node<K> {
        Node {
            address,
            node_type,
            entries: vec![],
            children: vec![],
            version: Version::V1(page_size),
            overflows: Vec::with_capacity(0),
        }
    }

    /// Loads a v1 node from memory at the given address.
    pub(super) fn load_v1<M: Memory>(
        header: NodeHeader,
        address: Address,
        max_key_size: u32,
        max_value_size: u32,
        memory: &M,
    ) -> Self {
        #[cfg(feature = "bench_scope")]
        let _p = canbench_rs::bench_scope("node_load_v1"); // May add significant overhead.

        // Load the entries.
        let mut entries = Vec::with_capacity(header.num_entries as usize);
        let mut offset = NodeHeader::size();
        for _ in 0..header.num_entries {
            let size = read_u32(memory, address + offset);
            let key = LazyKey::by_ref(offset, size);
            offset += U32_SIZE + Bytes::from(max_key_size);

            let size = read_u32(memory, address + offset);
            let value = LazyValue::by_ref(offset, size);
            offset += U32_SIZE + Bytes::from(max_value_size);

            entries.push((key, value));
        }

        // Load children if this is an internal node.
        let mut children = vec![];
        if header.node_type == INTERNAL_NODE_TYPE {
            // The number of children is equal to the number of entries + 1.
            children.reserve_exact(header.num_entries as usize + 1);
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
            version: Version::V1(DerivedPageSize {
                max_key_size,
                max_value_size,
            }),
            overflows: Vec::with_capacity(0),
        }
    }

    pub(super) fn save_v1<M: Memory>(&self, memory: &M) {
        #[cfg(feature = "bench_scope")]
        let _p = canbench_rs::bench_scope("node_save_v1"); // May add significant overhead.

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
        assert!(self
            .entries
            .windows(2)
            .all(|arr| self.get_key(&arr[0], memory) < self.get_key(&arr[1], memory)));

        let (max_key_size, max_value_size) = match self.version {
            Version::V1(DerivedPageSize {
                max_key_size,
                max_value_size,
            }) => (max_key_size, max_value_size),
            Version::V2 { .. } => unreachable!("cannot save v2 node as v1."),
        };

        let header = NodeHeader {
            magic: *MAGIC,
            version: LAYOUT_VERSION_1,
            node_type: match self.node_type {
                NodeType::Leaf => LEAF_NODE_TYPE,
                NodeType::Internal => INTERNAL_NODE_TYPE,
            },
            num_entries: self.entries.len() as u16,
        };

        write_struct(&header, self.address, memory);

        let mut offset = NodeHeader::size();

        // Load all the entries. This is necessary so that we don't overwrite referenced
        // entries when writing the entries to the node.
        for i in 0..self.entries.len() {
            self.entry(i, memory);
        }

        // Write the entries.
        for i in 0..self.entries.len() {
            // Write the size of the key.
            let key_bytes = self.key(i, memory).to_bytes_checked();
            write_u32(memory, self.address + offset, key_bytes.len() as u32);
            offset += U32_SIZE;

            // Write the key.
            write(memory, (self.address + offset).get(), key_bytes.borrow());
            offset += Bytes::from(max_key_size);

            // Write the size of the value.
            let value = self.value(i, memory);
            write_u32(memory, self.address + offset, value.len() as u32);
            offset += U32_SIZE;

            // Write the value.
            write(memory, (self.address + offset).get(), value);
            offset += Bytes::from(max_value_size);
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
}

/// Returns the size of a v1 node in bytes.
pub(super) fn size_v1(max_key_size: u32, max_value_size: u32) -> Bytes {
    let node_header_size = NodeHeader::size();
    let max_key_size = Bytes::from(max_key_size);
    let max_value_size = Bytes::from(max_value_size);
    let entry_size = U32_SIZE + max_key_size + max_value_size + U32_SIZE;
    let child_size = Address::size();

    node_header_size
        + Bytes::from(CAPACITY as u64) * entry_size
        + Bytes::from((CAPACITY + 1) as u64) * child_size
}
