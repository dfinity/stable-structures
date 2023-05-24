//! V2 of a B-Tree node.
//!
//! V2 evolves of V1 to make the insert and remove operations of a BTreeMap more efficient.
//! The primary difference in V2 is that entries in a node are not necessarily written in
//! sorted order. Entries can be written in the node in any order, and an "order array" is
//! introduced that stores the entry indices in sorted order.
//!
//! Not requiring entries to be written in sorted means that touching all the entries isn't
//! needed in the case of shifting. For example, consider a node that has the following keys:
//!
//! ```text
//! A - B - D - E - F - G`
//! ```
//!
//! Let's say we want to insert the key `C`. The node will then look like the following:
//!
//! ```text
//! A - B - C - D - E - F - G`
//! ```
//!
//! Notice that all entries from `C` onwards have shifted, and in V1 we'd have to reload and
//! rewrite keys `D` to `F`. In V2, these keys would be left completely untouched. Only the
//! order array would need to be updated.
//!
//! ## Compatibility
//!
//! V2 is _mostly_ backward compatible with V1, and the transition from V1 to V2 happens
//! automatically and invisibly. The only exception where the upgrade doesn't happen is if a node
//! has keys that are larger than `u16::MAX` in size.
//!
//! The reason for this limitation is that, to free up space for the order array, the maximum
//! allowed key size in V2 is `u16` rather than `u32`.
//!
//! ## Memory Layout
//!
//! The node is stored in stable memory with the following layout:
//!
//! ```text
//! --------------------------------------------------------------- <- Address 0
//! NodeHeader                            ↕ 7 bytes
//! ---------------------------------------------------------------
//! Reserved Space                        ↕ `CAPACITY` bytes
//! ---------------------------------------------------------------
//! Order Array                           ↕ `CAPACITY` bytes
//! --------------------------------------------------------------- <- Entries
//! Key 1's size (u16)                    ↕ 2 bytes
//! ---------------------------------------------------------------
//! Key 1's serialized bytes              ↕ `Key::MAX_SIZE bytes`
//! ---------------------------------------------------------------
//! Value 1's size (u32)                  ↕ 4 bytes
//! ---------------------------------------------------------------
//! Value 1's serialized bytes            ↕ `Value::MAX_SIZE bytes`
//! ---------------------------------------------------------------
//! ... (more entries - up to `CAPACITY` entries)
//! --------------------------------------------------------------- <- Children
//! Child 1's address                     ↕ 8 bytes
//! ---------------------------------------------------------------
//! Child 2's address                     ↕ 8 bytes
//! ---------------------------------------------------------------
//! ... (more children - up to `CAPACITY + 1` children)
//! ---------------------------------------------------------------
//! ```

use super::*;
use crate::btreemap::node::v1::entry_size_v1;

// header + order array size + extra bytes
const ENTRIES_OFFSET: Bytes = Bytes::new(7 + 2 * CAPACITY as u64);
const ORDER_ARRAY_OFFSET: Bytes = Bytes::new(7 + CAPACITY as u64);

impl<K: Storable + Ord + Clone> Node<K> {
    pub(super) fn load_v2<M: Memory>(
        address: Address,
        header: NodeHeader,
        memory: &M,
        max_key_size: u32,
        max_value_size: u32,
    ) -> Self {
        // Load the order array.
        // NOTE: Loading it as an array is faster than loading it as a vec.
        let order_array: [u8; CAPACITY] = read_struct(address + ORDER_ARRAY_OFFSET, memory);

        // Values are loaded lazily. Load references to each one.
        let encoded_values: Vec<_> = (0..header.num_entries as usize)
            .map(|i| Value::ByRef(order_array[i]))
            .collect();

        // Load the keys.
        let mut keys = Vec::with_capacity(header.num_entries as usize);
        let mut buf = Vec::with_capacity(max_key_size as usize);
        let entry_size = entry_size_v2(max_key_size, max_value_size);
        for idx in order_array.iter().take(header.num_entries as usize) {
            let mut offset = ENTRIES_OFFSET + Bytes::from(*idx) * entry_size;

            // Read the key's size.
            let key_size = read_u16(memory, address + offset);
            offset += U16_SIZE;

            // Read the key.
            buf.resize(key_size as usize, 0);
            memory.read((address + offset).get(), &mut buf);
            let key = K::from_bytes(Cow::Borrowed(&buf));
            keys.push(key);
        }

        // Load children if this is an internal node.
        let mut children = vec![];
        if header.node_type == INTERNAL_NODE_TYPE {
            let children_address =
                address + ENTRIES_OFFSET + entry_size * Bytes::from(CAPACITY as u64);
            let mut offset = Bytes::new(0);

            // The number of children is equal to the number of entries + 1.
            for _ in 0..header.num_entries + 1 {
                let child = Address::from(read_u64(memory, children_address + offset));
                offset += Address::size();
                children.push(child);
            }

            assert_eq!(children.len(), keys.len() + 1);
        }

        Self {
            address,
            keys,
            encoded_values: RefCell::new(encoded_values),
            children,
            node_type: match header.node_type {
                LEAF_NODE_TYPE => NodeType::Leaf,
                INTERNAL_NODE_TYPE => NodeType::Internal,
                other => unreachable!("Unknown node type {}", other),
            },
            max_key_size,
            max_value_size,
            version: Version::V2,
        }
    }

    /// Saves the node to memory based on the V2 layout.
    ///
    /// PRECONDITION:
    ///   * The node is at version 1 or 2.
    pub(super) fn save_v2<M: Memory>(&mut self, memory: &M) {
        // Assert precondition.
        debug_assert!(self.version == Version::V1 || self.version == Version::V2);

        if self.version == Version::V1 {
            // Migrate to the new layout. Eagerly load all the values.
            for idx in 0..self.entries_len() {
                self.value(idx, memory);
            }
        }

        let mut free_entry_indices = self.get_free_entry_indices();
        let mut order_array = vec![];

        // Write the entries.
        for (idx, key) in self.keys.iter().enumerate() {
            if let Value::ByRef(entry_idx) = self.encoded_values.borrow()[idx] {
                // The value is a reference, which means the entry hasn't been touched.
                // Add its entry index to the order array and skip saving it.
                order_array.push(entry_idx);
                continue;
            }

            // This is a new entry. Insert it at the next available free entry index.
            let entry_idx = free_entry_indices.pop().unwrap();

            let mut address = self.address
                + Self::get_entry_offset(
                    entry_idx,
                    self.max_key_size,
                    self.max_value_size,
                    Version::V2,
                );

            // Write the size of the key.
            let key_bytes = key.to_bytes();
            write_u16(memory, address, key_bytes.len() as u16);
            address += U16_SIZE;

            // Write the key.
            write(memory, address.get(), key_bytes.borrow());
            address += Bytes::from(self.max_key_size);

            // Write the size of the value.
            let value = self.value(idx, memory);
            write_u32(memory, address, value.len() as u32);
            address += U32_SIZE;

            // Write the value.
            write(memory, address.get(), &value);
            address += Bytes::from(self.max_value_size);

            order_array.push(entry_idx);
        }

        // Get the offset of the children. This line is a bit of a hack.
        let address = self.address
            + Self::get_entry_offset(
                CAPACITY as u8,
                self.max_key_size,
                self.max_value_size,
                self.version,
            );
        let mut offset = Bytes::new(0);

        // Write the children
        for child in self.children.iter() {
            write(memory, (address + offset).get(), &child.get().to_le_bytes());
            offset += Address::size();
        }

        // Write the order array.
        order_array.resize(CAPACITY, 0);
        let order_array: [u8; CAPACITY] = order_array.try_into().unwrap();
        write_struct(&order_array, self.address + ORDER_ARRAY_OFFSET, memory);

        // Update the version (is this necessary?)
        self.version = Version::V2;

        let header = NodeHeader {
            magic: *MAGIC,
            version: 2,
            node_type: match self.node_type {
                NodeType::Leaf => LEAF_NODE_TYPE,
                NodeType::Internal => INTERNAL_NODE_TYPE,
            },
            num_entries: self.keys.len() as u16,
        };

        write_struct(&header, self.address, memory);
    }

    // Returns a list of unused slot indices.
    fn get_free_entry_indices(&self) -> Vec<u8> {
        // Assume all entry indices are free.
        let mut free_entry_indices = vec![true; CAPACITY];

        // Iterate over the entries, seeing which indices are used.
        for val in self.encoded_values.borrow().iter() {
            if let Value::ByRef(idx) = val {
                // Mark the entry index as used.
                free_entry_indices[*idx as usize] = false;
            }
        }

        // Map the boolean array into a list of free entry indices.
        free_entry_indices
            .into_iter()
            .enumerate()
            .filter_map(|(idx, is_free)| if is_free { Some(idx as u8) } else { None })
            .collect()
    }

    pub(super) fn value_offset_v2(&self, idx: u8) -> Bytes {
        ENTRIES_OFFSET
            + entry_size_v2(self.max_key_size, self.max_value_size) * Bytes::from(idx)
            + key_size_v2(self.max_key_size)
    }

    fn get_entry_offset(
        idx: u8,
        max_key_size: u32,
        max_value_size: u32,
        version: Version,
    ) -> Bytes {
        match version {
            Version::V1 => {
                NodeHeader::size() + Bytes::from(idx) * entry_size_v1(max_key_size, max_value_size)
            }
            Version::V2 => {
                ENTRIES_OFFSET + Bytes::from(idx) * entry_size_v2(max_key_size, max_value_size)
            }
        }
    }
}

// The number of bytes needed to store an entry in the node with the V2 layout.
fn entry_size_v2(max_key_size: u32, max_value_size: u32) -> Bytes {
    key_size_v2(max_key_size) + value_size_v2(max_value_size)
}

// The number of bytes needed to store a key in the node.
fn key_size_v2(max_key_size: u32) -> Bytes {
    U16_SIZE + Bytes::from(max_key_size)
}

// The number of bytes needed to store a value in the node.
fn value_size_v2(max_value_size: u32) -> Bytes {
    U32_SIZE + Bytes::from(max_value_size)
}
