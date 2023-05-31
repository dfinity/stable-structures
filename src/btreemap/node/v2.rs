use super::*;

impl<K: Storable + Ord + Clone> Node<K> {
    // Loads a node from memory at the given address.
    pub(super) fn load_v2<M: Memory>(address: Address, page_size: u32, memory: &M) -> Self {
        //println!("load v2");

        // Read the node into a buffer.
        let mut full_buf = vec![0; page_size as usize];
        memory.read(address.get(), &mut full_buf);

        // Concatenate the overflow page into the buffer.
        let mut buf = vec![0; 8];
        memory.read((address + OVERFLOW_OFFSET).get(), &mut buf);
        let overflow_address = Address::from(u64::from_le_bytes(buf.try_into().unwrap()));

        let mut overflow_buf = vec![0; page_size as usize];
        memory.read(overflow_address.get(), &mut overflow_buf);
        // TODO: validate magic, read next overflow.
        full_buf.extend_from_slice(&overflow_buf[OVERFLOW_OVERHEAD.get() as usize..]);

        // Load the metadata.
        let mut offset = META_DATA_OFFSET;
        let mut buf = vec![0];
        let node_type = match full_buf[offset.get() as usize] {
            LEAF_NODE_TYPE => NodeType::Leaf,
            INTERNAL_NODE_TYPE => NodeType::Internal,
            other => unreachable!("Unknown node type {}", other),
        };

        offset += Bytes::new(1);
        buf.resize(2, 0);
        let num_entries = u16::from_le_bytes(
            (&full_buf[offset.get() as usize..offset.get() as usize + 2])
                .try_into()
                .unwrap(),
        ) as usize;
        offset += Bytes::new(2);

        // Read overflow
        buf.resize(8, 0);

        // Load the entries.
        let mut keys = Vec::with_capacity(num_entries);
        let mut encoded_values = Vec::with_capacity(num_entries);
        let mut offset = ENTRIES_OFFSET_V2;
        let mut buf = vec![]; //Vec::with_capacity(max_key_size.max(max_value_size) as usize);
        for _ in 0..num_entries {
            // Read the key's size.
            let key_size = read_u32(memory, address + offset);
            offset += U32_SIZE;

            // Read the key.
            buf.resize(key_size as usize, 0);
            let key = K::from_bytes(Cow::Borrowed(
                &full_buf[offset.get() as usize..offset.get() as usize + key_size as usize],
            ));
            offset += Bytes::from(key_size);
            keys.push(key);
        }

        // Load the values
        for _ in 0..num_entries {
            // Read the value's size.
            //    let value_size = read_u32(memory, get_address(offset));
            let value_size = u32::from_le_bytes(
                (&full_buf[offset.get() as usize..offset.get() as usize + 4])
                    .try_into()
                    .unwrap(),
            );
            offset += U32_SIZE;

            //            println!("value size: {value_size}");

            // TODO Values are loaded lazily. Store a reference and skip loading it.
            buf.resize(value_size as usize, 0);
            encoded_values.push(Value::ByVal(
                full_buf[offset.get() as usize..offset.get() as usize + value_size as usize]
                    .to_vec(),
            ));

            //println!("values: {:?}", encoded_values);
            offset += value_size.into();
        }

        // Load children if this is an internal node.
        let mut children = vec![];
        if node_type == NodeType::Internal {
            // The number of children is equal to the number of entries + 1.
            for _ in 0..num_entries + 1 {
                //   let child = Address::from(read_u64(memory, get_address(offset)));
                let child = Address::from(u64::from_le_bytes(
                    (&full_buf[offset.get() as usize..offset.get() as usize + 8])
                        .try_into()
                        .unwrap(),
                ));
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
            node_type,
            version: Version::V2 { page_size },
            overflow: if overflow_address == crate::types::NULL {
                None
            } else {
                Some(overflow_address)
            },
        }
    }

    // Saves the node to memory.
    pub(super) fn save_v2<M: Memory>(&self, allocator: &mut Allocator<M>) {
        // A buffer to serialize the node into first, then write to memory.
        let mut buf = vec![];
        buf.extend_from_slice(MAGIC);
        buf.extend_from_slice(&[LAYOUT_VERSION_2]);
        buf.push(match self.node_type {
            NodeType::Leaf => LEAF_NODE_TYPE,
            NodeType::Internal => INTERNAL_NODE_TYPE,
        });
        buf.extend_from_slice(&(self.keys.len() as u16).to_le_bytes());

        // TODO: write the overflow pointer here.
        buf.extend_from_slice(&[0; 8]);

        let memory = allocator.memory();

        // Load all the values. This is necessary so that we don't overwrite referenced
        // values when writing the entries to the node.
        for i in 0..self.keys.len() {
            self.value(i, memory);
        }

        // Write the entries.
        for key in self.keys.iter() {
            // Write the size of the key.
            let key_bytes = key.to_bytes();
            buf.extend_from_slice(&(key_bytes.len() as u32).to_le_bytes());

            // Write the key.
            buf.extend_from_slice(key_bytes.borrow());
        }

        assert_eq!(self.keys.len(), self.encoded_values.borrow().len());

        for idx in 0..self.entries_len() {
            // Write the size of the value.
            let value = self.value(idx, memory);
            buf.extend_from_slice(&(value.len() as u32).to_le_bytes());

            // Write the value.
            buf.extend_from_slice(&value);
        }

        // Write the children
        for child in self.children.iter() {
            buf.extend_from_slice(&child.get().to_le_bytes());
        }

        let page_size = if let Version::V2 { page_size } = self.version {
            page_size
        } else {
            unreachable!()
        };

        self.write_paginated(buf, allocator, page_size as usize);
    }

    fn write_paginated<M: Memory>(
        &self,
        mut buf: Vec<u8>,
        allocator: &mut Allocator<M>,
        page_size: usize,
    ) {
        if buf.len() > page_size {
            let additional_pages_needed =
                1 + (buf.len() - page_size) / (page_size - OVERFLOW_OVERHEAD.get() as usize);

            if self.overflow == None {
                // Allocate a new overflow.
                let overflow_address = allocator.allocate();

                //println!("overflowed. allocated address {overflow_address:?}");

                // Update buffer to include offset address.
                buf[OVERFLOW_OFFSET.get() as usize..OVERFLOW_OFFSET.get() as usize + 8]
                    .copy_from_slice(overflow_address.get().to_le_bytes().as_slice());

                let memory = allocator.memory();
                memory.write(overflow_address.get(), OVERFLOW_MAGIC);

                // Write a NULL to indicate that there are no more overflows.
                memory.write(overflow_address.get() + Bytes::new(3).get(), &[0; 8]);

                // Write the first page
                memory.write(self.address.get(), &buf[..page_size]);

                // Write the remaining buf
                memory.write(
                    (overflow_address + OVERFLOW_OVERHEAD).get(),
                    &buf[page_size..],
                );
            } else {
                panic!("support overflow existing");
            }
        } else {
            let memory = allocator.memory();

            memory.write(self.address.get(), &buf);
        }
    }
}
