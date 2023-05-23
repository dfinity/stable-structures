use super::*;

impl<K: Storable + Ord + Clone> Node<K> {
    pub(super) fn load_v2<M: Memory>(
        address: Address,
        header: NodeHeader,
        memory: &M,
        max_key_size: u32,
        max_value_size: u32,
    ) -> Self {
        // Load the cell array.
        let cell_array: [u8; CAPACITY] = read_struct(address + NodeHeader::size(), memory);

        // Load the entries.
        let encoded_values: Vec<_> = (0..header.num_entries as usize)
            .map(|i| Value::ByRef(cell_array[i]))
            .collect();
        let mut keys = Vec::with_capacity(header.num_entries as usize);
        let mut buf = Vec::with_capacity(max_key_size.max(max_value_size) as usize);
        let entries_offset = NodeHeader::size() + Bytes::new(2 * CAPACITY as u64);
        let entry_size = (max_key_size + 2 + max_value_size + 4) as u64;
        for i in 0..header.num_entries as usize {
            let idx = cell_array[i];
            let mut offset = entries_offset + Bytes::new(idx as u64 * entry_size);

            // Read the key's size.
            let key_size = read_u16(memory, address + offset);
            offset += U16_SIZE;

            // Read the key.
            buf.resize(key_size as usize, 0);
            memory.read((address + offset).get(), &mut buf);
            let key = K::from_bytes(Cow::Borrowed(&buf));
            keys.push(key);
        }

        // Get the offset of the children. This line is a bit of a hack.
        let children_address = address
                    + NodeHeader::size()
                    + Bytes::new(2 * CAPACITY as u64) /* the cell array size */
                    + Bytes::new(
                        (CAPACITY as u32 * (max_key_size + 2 + max_value_size + 4)
                    ) as u64);

        let mut offset = Bytes::new(0);

        // Load children if this is an internal node.
        let mut children = vec![];
        if header.node_type == INTERNAL_NODE_TYPE {
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
            version: header.version,
        }
    }

    /// Saves the node to memory.
    pub fn save_v2<M: Memory>(&mut self, memory: &M) {
        let mut free_slots = self.get_free_slots();

        let mut cell_array = vec![];

        // Write the entries.
        for (idx, key) in self.keys.iter().enumerate() {
            // TODO: borrow outside?
            if let Value::ByRef(slot_idx) = self.encoded_values.borrow()[idx] {
                // Value hasn't been touched. Add idx to cell array and skip writing the keys and
                // values.
                cell_array.push(slot_idx);
                continue;
            }

            // This is a new entry. Insert it at the next available free slot.

            let free_slot_idx = free_slots.pop().unwrap();

            cell_array.push(free_slot_idx);

            let mut address = self.address
                + Self::get_entry_offset(
                    free_slot_idx as usize,
                    self.max_key_size,
                    self.max_value_size,
                    self.version,
                );

            // Write the size of the key.
            let key_bytes = key.to_bytes();
            // TODO: asset key size.
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
        }

        // Get the offset of the children. This line is a bit of a hack.
        let address = self.address
            + Self::get_entry_offset(
                CAPACITY,
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

        // Write the cell array.
        cell_array.resize(CAPACITY, 0);
        let cell_array: [u8; CAPACITY] = cell_array.try_into().unwrap();
        write_struct(&cell_array, self.address + NodeHeader::size(), memory);

        // Update the version (is this necessary?)
        self.version = 2;

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
}
