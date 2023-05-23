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
}
