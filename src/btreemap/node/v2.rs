use super::*;

const PAGE_OVERFLOW_NEXT_OFFSET: Bytes = Bytes::new(3);
const PAGE_OVERFLOW_DATA_OFFSET: Bytes = Bytes::new(11); // magic + next address

use crate::types::NULL;
use crate::write_u64;

impl<K: Storable + Ord + Clone> Node<K> {
    // Loads a node from memory at the given address.
    pub(super) fn load_v2<M: Memory>(address: Address, page_size: u32, memory: &M) -> Self {
        println!("LOADING {:?}...", address);
        // Read the node into a buffer.
        let mut full_buf = vec![0; page_size as usize];
        memory.read(address.get(), &mut full_buf);

        let mut overflow_address = Address::from(read_u64(memory, address + OVERFLOW_OFFSET));

        let original_overflow_address = overflow_address;

        // Concatenate the overflow page into the buffer.
        loop {
            if overflow_address == NULL {
                break;
            }
            println!("overflow address: {:?}", overflow_address);

            let mut overflow_buf = vec![0; page_size as usize];

            memory.read(overflow_address.get(), &mut overflow_buf);
            // TODO: validate magic, read next overflow.
            full_buf.extend_from_slice(&overflow_buf[PAGE_OVERFLOW_DATA_OFFSET.get() as usize..]);

            overflow_address = Address::from(read_u64(
                memory,
                overflow_address + PAGE_OVERFLOW_NEXT_OFFSET,
            ));
        }

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
        let mut offset = ENTRIES_OFFSET_V2.get() as usize;
        let mut buf = vec![]; //Vec::with_capacity(max_key_size.max(max_value_size) as usize);
        for _ in 0..num_entries {
            // Read the key's size.
            let key_size =
                u32::from_le_bytes((&full_buf[offset..offset + 4]).try_into().unwrap()) as usize;
            offset += 4;

            // Read the key.
            buf.resize(key_size as usize, 0);
            let key = K::from_bytes(Cow::Borrowed(&full_buf[offset..offset + key_size]));
            offset += key_size;
            keys.push(key);
        }

        // Load the values
        for _ in 0..num_entries {
            // Read the value's size.
            //    let value_size = read_u32(memory, get_address(offset));
            let value_size =
                u32::from_le_bytes((&full_buf[offset..offset + 4]).try_into().unwrap()) as usize;
            offset += 4;

            // TODO Values are loaded lazily. Store a reference and skip loading it.
            buf.resize(value_size as usize, 0);
            encoded_values.push(Value::ByVal(full_buf[offset..offset + value_size].to_vec()));

            offset += value_size;
        }

        // Load children if this is an internal node.
        let mut children = vec![];
        if node_type == NodeType::Internal {
            // The number of children is equal to the number of entries + 1.
            for _ in 0..num_entries + 1 {
                //   let child = Address::from(read_u64(memory, get_address(offset)));
                let child = Address::from(u64::from_le_bytes(
                    (&full_buf[offset..offset + 8]).try_into().unwrap(),
                ));
                offset += 8; //Address::size();
                children.push(child);
            }

            assert_eq!(children.len(), keys.len() + 1);
        }

        println!("original overflow address: {:?}", original_overflow_address);
        println!("DONE");
        Self {
            address,
            keys,
            encoded_values: RefCell::new(encoded_values),
            children,
            node_type,
            version: Version::V2 { page_size },
            overflow: if original_overflow_address == crate::types::NULL {
                None
            } else {
                Some(original_overflow_address)
            },
        }
    }

    // Saves the node to memory.
    pub(super) fn save_v2<M: Memory>(&self, allocator: &mut Allocator<M>) {
        println!("SAVING {:?}...", self.address);
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
        println!("DONE");
    }

    fn write_paginated<M: Memory>(
        &self,
        mut buf: Vec<u8>,
        allocator: &mut Allocator<M>,
        page_size: usize,
    ) {
        // Compute how many overflow pages are needed.
        let additional_pages_needed = if buf.len() > page_size {
            let overflow_size = (page_size - PAGE_OVERFLOW_DATA_OFFSET.get() as usize);
            let data_size = buf.len() - page_size;

            // Ceiling division
            (data_size + overflow_size - 1) / overflow_size
        } else {
            0
        };

        //       println!("overflow pages needed: {:?}", additional_pages_needed);
        //       println!("buffer size: {}", buf.len());

        // Get overflow addresses, making the necessary allocation/deallocations.
        let overflow_addresses =
            self.get_overflow_addresses_rename(additional_pages_needed, allocator);

        //        println!("overflow addresses: {:?}", overflow_addresses);

        // Write the first page
        let memory = allocator.memory();
        memory.write(
            self.address.get(),
            &buf[..std::cmp::min(page_size, buf.len())],
        );
        if overflow_addresses.len() > 0 {
            // Update the page to write the next overflow address.

            //memory.write(self.address.get(), &buf[..page_size]);
            write_u64(
                memory,
                self.address + OVERFLOW_OFFSET,
                overflow_addresses[0].get(),
            );
        }

        let mut next_idx = page_size;
        let mut i = 0;

        let data_size = page_size - PAGE_OVERFLOW_DATA_OFFSET.get() as usize;
        while next_idx < buf.len() {
            //         println!("writing page at address {:?}", overflow_addresses[i].get());
            // Write magic and next address
            memory.write(overflow_addresses[i].get(), &OVERFLOW_MAGIC[..]);
            let next_address = overflow_addresses.get(i + 1).unwrap_or(&NULL);
            //        println!(
            //            "The next address of {:?} is {:?}",
            //           overflow_addresses[i] + PAGE_OVERFLOW_NEXT_OFFSET,
            //           next_address.get()
            //      );
            write_u64(
                memory,
                overflow_addresses[i] + PAGE_OVERFLOW_NEXT_OFFSET,
                next_address.get(),
            );

            // Write the data from the buffer
            let start_idx = page_size + i * data_size;
            let end_idx = std::cmp::min(buf.len(), page_size + (i + 1) * data_size);
            memory.write(
                (overflow_addresses[i] + PAGE_OVERFLOW_DATA_OFFSET).get(),
                &buf[start_idx..end_idx],
            );
            //        println!("buf write bytes from {} to {}", start_idx, end_idx);

            i += 1;
            next_idx += data_size;
        }
    }

    fn get_overflow_addresses_rename<M: Memory>(
        &self,
        num_overflow_pages: usize,
        allocator: &mut Allocator<M>,
    ) -> Vec<Address> {
        // Fetch the overflow page addresses of this node.
        let mut current_overflow_addresses = self.get_overflow_addresses(allocator.memory());

        // If there are too many overflow addresses, deallocate some until we've reached
        // the number we need.
        while current_overflow_addresses.len() > num_overflow_pages {
            println!("1. DEALLOCATING");
            let overflow_page = current_overflow_addresses.pop().unwrap();
            allocator.deallocate(overflow_page);
        }

        // Allocate more pages to accommodate the number requested, if needed.
        while current_overflow_addresses.len() < num_overflow_pages {
            println!("1. ALLOCATING");
            current_overflow_addresses.push(allocator.allocate());
        }

        current_overflow_addresses
    }

    pub(super) fn get_overflow_addresses<M: Memory>(&self, memory: &M) -> Vec<Address> {
        println!("getting overflow addresses");
        let mut overflow_addresses = vec![];
        let mut next = self.overflow;
        while let Some(overflow_address) = next {
            overflow_addresses.push(overflow_address);

            // Load next overflow address.
            let maybe_next = Address::from(read_u64(
                memory,
                overflow_address + PAGE_OVERFLOW_NEXT_OFFSET,
            ));

            if maybe_next == crate::types::NULL {
                next = None;
            } else {
                next = Some(maybe_next);
            }
        }

        println!("DONE");
        overflow_addresses
    }
}
