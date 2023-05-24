use super::*;

impl<K: Storable + Ord + Clone> Node<K> {
    pub(super) fn load_v1<M: Memory>(
        address: Address,
        header: NodeHeader,
        memory: &M,
        max_key_size: u32,
        max_value_size: u32,
    ) -> Self {
        // Load the entries.
        let mut keys = Vec::with_capacity(header.num_entries as usize);
        let mut encoded_values = Vec::with_capacity(header.num_entries as usize);
        let mut offset = NodeHeader::size();
        let mut buf = Vec::with_capacity(max_key_size as usize);
        for i in 0..header.num_entries {
            // Read the key's size.
            let key_size = read_u32(memory, address + offset);
            offset += U32_SIZE;

            // Read the key.
            buf.resize(key_size as usize, 0);
            memory.read((address + offset).get(), &mut buf);
            offset += Bytes::from(max_key_size);
            let key = K::from_bytes(Cow::Borrowed(&buf));
            keys.push(key);

            // Values are loaded lazily. Store a reference and skip loading it.
            encoded_values.push(Value::ByRef(i as u8));
            offset += U32_SIZE + Bytes::from(max_value_size);
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
            encoded_values: RefCell::new(encoded_values),
            children,
            node_type: match header.node_type {
                LEAF_NODE_TYPE => NodeType::Leaf,
                INTERNAL_NODE_TYPE => NodeType::Internal,
                other => unreachable!("Unknown node type {}", other),
            },
            max_key_size,
            max_value_size,
            version: Version::V1.into(),
        }
    }

    pub(super) fn save_v1<M: Memory>(&self, memory: &M) {
        let header = NodeHeader {
            magic: *MAGIC,
            version: LAYOUT_VERSION_1,
            node_type: match self.node_type {
                NodeType::Leaf => LEAF_NODE_TYPE,
                NodeType::Internal => INTERNAL_NODE_TYPE,
            },
            num_entries: self.keys.len() as u16,
        };

        write_struct(&header, self.address, memory);

        let mut offset = NodeHeader::size();

        // Load all the values. This is necessary so that we don't overwrite referenced
        // values when writing the entries to the node.
        for i in 0..self.keys.len() {
            self.value(i, memory);
        }

        // Write the entries.
        for (idx, key) in self.keys.iter().enumerate() {
            // Write the size of the key.
            let key_bytes = key.to_bytes();
            write_u32(memory, self.address + offset, key_bytes.len() as u32);
            offset += U32_SIZE;

            // Write the key.
            write(memory, (self.address + offset).get(), key_bytes.borrow());
            offset += Bytes::from(self.max_key_size);

            // Write the size of the value.
            let value = self.value(idx, memory);
            write_u32(memory, self.address + offset, value.len() as u32);
            offset += U32_SIZE;

            // Write the value.
            write(memory, (self.address + offset).get(), &value);
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

    pub(super) fn value_offset_v1(&self, idx: u8) -> Bytes {
        NodeHeader::size()
            + Bytes::from(idx) * entry_size_v1(self.max_key_size, self.max_value_size)
            + value_size_v1(self.max_value_size)
    }
}

// The number of bytes needed to store an entry in the node with the V1 layout.
pub(super) fn entry_size_v1(max_key_size: u32, max_value_size: u32) -> Bytes {
    key_size_v1(max_key_size) + value_size_v1(max_value_size)
}

// The number of bytes needed to store a key in the node.
fn key_size_v1(max_key_size: u32) -> Bytes {
    U32_SIZE + Bytes::from(max_key_size)
}

// The number of bytes needed to store a value in the node.
fn value_size_v1(max_value_size: u32) -> Bytes {
    U32_SIZE + Bytes::from(max_value_size)
}
