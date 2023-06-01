use super::*;

// The offset where the address of the overflow page is present.
const OVERFLOW_ADDRESS_OFFSET: Bytes = Bytes::new(7);
const ENTRIES_OFFSET: Bytes = Bytes::new(15); // an additional 8 bytes for the overflow pointer

const PAGE_OVERFLOW_NEXT_OFFSET: Bytes = Bytes::new(3);
const PAGE_OVERFLOW_DATA_OFFSET: Bytes = Bytes::new(11); // magic + next address
                                                         //
const OVERFLOW_MAGIC: &[u8; 3] = b"NOF";

use crate::types::NULL;
use crate::write_u64;

impl<K: Storable + Ord + Clone> Node<K> {
    // Loads a V2 node from memory at the given address.
    pub(super) fn load_v2<M: Memory>(address: Address, page_size: u32, memory: &M) -> Self {
        let full_buf = read_node(address, page_size as usize, memory);

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
        let mut offset = ENTRIES_OFFSET;
        let mut buf = vec![];
        for _ in 0..num_entries {
            // Read the key's size.
            let key_size = read_u32_from_slice(&full_buf, offset) as usize;
            offset += U32_SIZE;

            // Read the key.
            buf.resize(key_size, 0);
            let key = K::from_bytes(Cow::Borrowed(
                &full_buf[offset.get() as usize..offset.get() as usize + key_size],
            ));
            offset += Bytes::from(key_size as u64);
            keys.push(key);
        }

        // Load the values
        for _ in 0..num_entries {
            // Read the value's size.
            let value_size = read_u32_from_slice(&full_buf, offset) as usize;
            offset += U32_SIZE;

            // Read the value.
            // TODO: Read values lazily.
            buf.resize(value_size, 0);
            encoded_values.push(Value::ByVal(
                full_buf[offset.get() as usize..offset.get() as usize + value_size].to_vec(),
            ));

            offset += Bytes::from(value_size as u64);
        }

        // Load children if this is an internal node.
        let mut children = vec![];
        if node_type == NodeType::Internal {
            // The number of children is equal to the number of entries + 1.
            for _ in 0..num_entries + 1 {
                let child = address_from_slice(&full_buf, offset);
                offset += Address::size();
                children.push(child);
            }

            assert_eq!(children.len(), keys.len() + 1);
        }

        let original_overflow_address = address_from_slice(&full_buf, OVERFLOW_ADDRESS_OFFSET);

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
    pub(super) fn save_v2<M: Memory>(&self, page_size: u32, allocator: &mut Allocator<M>) {
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

        self.write_paginated(buf, allocator, page_size as usize);
    }

    fn write_paginated<M: Memory>(
        &self,
        buf: Vec<u8>,
        allocator: &mut Allocator<M>,
        page_size: usize,
    ) {
        // Compute how many overflow pages are needed.
        let additional_pages_needed = if buf.len() > page_size {
            let overflow_size = page_size - PAGE_OVERFLOW_DATA_OFFSET.get() as usize;
            let data_size = buf.len() - page_size;

            // Ceiling division
            (data_size + overflow_size - 1) / overflow_size
        } else {
            0
        };

        // Get overflow addresses, making the necessary allocation/deallocations.
        let overflow_addresses =
            self.get_overflow_addresses_rename(additional_pages_needed, allocator);

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
                self.address + OVERFLOW_ADDRESS_OFFSET,
                overflow_addresses[0].get(),
            );
        }

        let mut next_idx = page_size;
        let mut i = 0;

        let data_size = page_size - PAGE_OVERFLOW_DATA_OFFSET.get() as usize;
        while next_idx < buf.len() {
            // Write magic and next address
            memory.write(overflow_addresses[i].get(), &OVERFLOW_MAGIC[..]);
            let next_address = overflow_addresses.get(i + 1).unwrap_or(&NULL);
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
            let overflow_page = current_overflow_addresses.pop().unwrap();
            allocator.deallocate(overflow_page);
        }

        // Allocate more pages to accommodate the number requested, if needed.
        while current_overflow_addresses.len() < num_overflow_pages {
            current_overflow_addresses.push(allocator.allocate());
        }

        current_overflow_addresses
    }

    pub(super) fn get_overflow_addresses<M: Memory>(&self, memory: &M) -> Vec<Address> {
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

        overflow_addresses
    }
}

// Reads the entirety of the node, including all its overflows, into a buffer.
fn read_node<M: Memory>(address: Address, page_size: usize, memory: &M) -> Vec<u8> {
    // Read the first page of the node.
    let mut buf = vec![0; page_size];
    memory.read(address.get(), &mut buf);

    // Append overflow pages, if any.
    let mut overflow_address = address_from_slice(&buf, OVERFLOW_ADDRESS_OFFSET);
    while overflow_address != NULL {
        // Read the overflow.
        let mut overflow_buf = vec![0; page_size];
        memory.read(overflow_address.get(), &mut overflow_buf);

        // Validate the magic of the overflow.
        assert_eq!(&overflow_buf[0..3], OVERFLOW_MAGIC, "Bad magic.");

        // Read the next address
        overflow_address = address_from_slice(&overflow_buf, PAGE_OVERFLOW_NEXT_OFFSET);

        // Append its data to the buffer.
        buf.extend_from_slice(&overflow_buf[PAGE_OVERFLOW_DATA_OFFSET.get() as usize..]);
    }

    buf
}

fn read_u64_from_slice(slice: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes((&slice[offset..offset + 8]).try_into().unwrap())
}

fn read_u32_from_slice(slice: &[u8], offset: Bytes) -> u32 {
    u32::from_le_bytes(
        (&slice[offset.get() as usize..offset.get() as usize + 4])
            .try_into()
            .unwrap(),
    )
}

fn address_from_slice(slice: &[u8], offset: Bytes) -> Address {
    Address::from(read_u64_from_slice(slice, offset.get() as usize))
}
