use super::*;

impl<K: Storable + Ord + Clone> Node<K> {
    /// Creates a new V1 node at the given address.
    pub(super) fn new_v1(
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
            version: Version::V1 {
                max_key_size,
                max_value_size,
            },
            overflow: None,
        }
    }

    /// Loads a node from memory at the given address.
    pub(super) fn load_v1<M: Memory>(
        address: Address,
        max_key_size: u32,
        max_value_size: u32,
        memory: &M,
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
            offset += Bytes::from(max_key_size);
            let key = K::from_bytes(Cow::Borrowed(&buf));
            keys.push(key);

            // Values are loaded lazily. Store a reference and skip loading it.
            encoded_values.push(Value::ByRef(offset));
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
            version: Version::V1 {
                max_key_size,
                max_value_size,
            },
            overflow: None,
        }
    }

    pub(super) fn save_v1<M: Memory>(&self, memory: &M) {
        let (max_key_size, max_value_size) = match self.version {
            Version::V1 {
                max_key_size,
                max_value_size,
            } => (max_key_size, max_value_size),
            Version::V2 { .. } => unreachable!("cannot save v2 node as v1."),
        };

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
            offset += Bytes::from(max_key_size);

            // Write the size of the value.
            let value = self.value(idx, memory);
            write_u32(memory, self.address + offset, value.len() as u32);
            offset += U32_SIZE;

            // Write the value.
            write(memory, (self.address + offset).get(), &value);
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
///
/// See the documentation of [`Node`] for the memory layout.
pub(super) fn size_v1(max_key_size: u32, max_value_size: u32) -> Bytes {
    let max_key_size = Bytes::from(max_key_size);
    let max_value_size = Bytes::from(max_value_size);

    let node_header_size = NodeHeader::size();
    let entry_size = U32_SIZE + max_key_size + max_value_size + U32_SIZE;
    let child_size = Address::size();

    node_header_size
        + Bytes::from(CAPACITY as u64) * entry_size
        + Bytes::from((CAPACITY + 1) as u64) * child_size
}
