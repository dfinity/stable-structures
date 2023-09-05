//! Node V2
//!
//! A v2 node is an iteration on a v1 node. Compared to a v1 node, it has a
//! smaller memory footprint and support for unbounded types.
//!
//! # Memory Layout
//!
//! To support unbounded types, a v2 node is variable in size and can span multiple
//! pages of memory if needed [^note]. There are two types of pages:
//!
//! 1. Initial Page (the first page of the node)
//! 2. Overflow page (subsequent pages of the node)
//!
//! ## Initial Page Memory Layout
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
//! ----------------------------------------
//! Overflow address        ↕ 8 bytes
//! ---------------------------------------- <-- Children (Address 15)
//! Child(0) address        ↕ 8 bytes
//! ----------------------------------------
//! ...
//! ----------------------------------------
//! Child(k + 1) address    ↕ 8 bytes
//! ---------------------------------------- <-- Keys
//! Key(0)
//! ----------------------------------------
//! ...
//! ----------------------------------------
//! Key(k)
//! ---------------------------------------- <-- Values
//! Value(0)
//! ----------------------------------------
//! ...
//! ----------------------------------------
//! Value(k)
//! ----------------------------------------
//! ```
//!
//! ## Overflow Page Memory Layout
//!
//! If the data to be stored in the initial page layout is larger than the page size,
//! then overflow pages are used.
//!
//! ```text
//! ----------------------------------------
//! Magic "NOF"             ↕ 3 bytes
//! ----------------------------------------
//! Next address            ↕ 8 byte
//! ----------------------------------------
//! Data
//! ----------------------------------------
//! ```
//!
//! ## Keys and Values
//! Keys and values are both encoded in memory as blobs.
//!
//! If they are variable in size (i.e. their `IS_FIXED` attribute is set to false),
//! then the size of the blob is encoded before the blob itself. Otherwise, no size
//! information is stored.
//!
//! [^note]: The page here refers to a fixed-size chunk of memory that is provided to the
//! node by the BTreeMap Allocator, and has no connection with OS memory pages or
//! Wasm pages.

use super::*;
use crate::btreemap::Allocator;
use crate::types::NULL;
use crate::write_u64;
use std::cmp::min;

// Initial page
const LAYOUT_VERSION_2: u8 = 2;
const NODE_TYPE_OFFSET: usize = 4;
const NUM_ENTRIES_OFFSET: usize = 5;
const OVERFLOW_ADDRESS_OFFSET: Bytes = Bytes::new(7);
const ENTRIES_OFFSET: Bytes = Bytes::new(15);

// Overflow page
const OVERFLOW_MAGIC: &[u8; 3] = b"NOF";
const PAGE_OVERFLOW_NEXT_OFFSET: Bytes = Bytes::new(3);
const PAGE_OVERFLOW_DATA_OFFSET: Bytes = Bytes::new(11);

// The minimum size a page can have.
// Rationale: a page size needs to at least store the header (15 bytes) + all the children
// addresses (88 bytes). We round that up to 128 to get a nice binary number.
const MINIMUM_PAGE_SIZE: u32 = 128;

impl<K: Storable + Ord + Clone> Node<K> {
    /// Creates a new v2 node at the given address.
    pub fn new_v2(address: Address, node_type: NodeType, page_size: PageSize) -> Node<K> {
        assert!(page_size.get() >= MINIMUM_PAGE_SIZE);

        Node {
            address,
            node_type,
            version: Version::V2(page_size),
            keys: vec![],
            encoded_values: RefCell::default(),
            children: vec![],
            overflow: None,
        }
    }

    /// Loads a v2 node from memory at the given address.
    pub(super) fn load_v2<M: Memory>(address: Address, page_size: PageSize, memory: &M) -> Self {
        // Load the node, including any overflows, into a buffer.
        let node_buf = read_node(address, page_size.get(), memory);

        // Load the node type.
        let node_type = match node_buf[NODE_TYPE_OFFSET] {
            LEAF_NODE_TYPE => NodeType::Leaf,
            INTERNAL_NODE_TYPE => NodeType::Internal,
            other => unreachable!("Unknown node type {}", other),
        };

        // Load the number of entries
        let num_entries = read_u16_from_slice(&node_buf, NUM_ENTRIES_OFFSET) as usize;

        // Load children if this is an internal node.
        let mut offset = ENTRIES_OFFSET;
        let mut children = vec![];
        if node_type == NodeType::Internal {
            // The number of children is equal to the number of entries + 1.
            for _ in 0..num_entries + 1 {
                let child = address_from_slice(&node_buf, offset);
                offset += Address::size();
                children.push(child);
            }
        }

        // Load the keys.
        let mut keys = Vec::with_capacity(num_entries);
        let mut encoded_values = Vec::with_capacity(num_entries);
        let mut buf = vec![];
        for _ in 0..num_entries {
            // Load the key's size.
            // TODO: store the size in a more efficient way.
            // TODO: don't store the size if the key is fixed.
            let key_size = read_u32_from_slice(&node_buf, offset) as usize;
            offset += U32_SIZE;

            // Load the key.
            buf.resize(key_size, 0);
            let key = K::from_bytes(Cow::Borrowed(
                &node_buf[offset.get() as usize..offset.get() as usize + key_size],
            ));
            offset += Bytes::from(key_size as u64);
            keys.push(key);
        }

        // Load the values
        for _ in 0..num_entries {
            // Load the value's size.
            let value_size = read_u32_from_slice(&node_buf, offset) as usize;
            offset += U32_SIZE;

            // Load the value.
            // TODO: Read values lazily.
            buf.resize(value_size, 0);
            encoded_values.push(Value::ByVal(
                node_buf[offset.get() as usize..offset.get() as usize + value_size].to_vec(),
            ));

            offset += Bytes::from(value_size as u64);
        }

        let original_overflow_address = address_from_slice(&node_buf, OVERFLOW_ADDRESS_OFFSET);

        Self {
            address,
            keys,
            encoded_values: RefCell::new(encoded_values),
            children,
            node_type,
            version: Version::V2(page_size),
            overflow: if original_overflow_address == crate::types::NULL {
                None
            } else {
                Some(original_overflow_address)
            },
        }
    }

    // Saves the node to memory.
    pub(super) fn save_v2<M: Memory>(&self, allocator: &mut Allocator<M>) {
        let page_size = self.version.page_size().get();
        assert!(page_size >= MINIMUM_PAGE_SIZE);
        assert_eq!(self.keys.len(), self.encoded_values.borrow().len());

        // A buffer to serialize the node into first, then write to memory.
        let mut buf = vec![];
        buf.extend_from_slice(MAGIC);
        buf.extend_from_slice(&[LAYOUT_VERSION_2]);
        buf.push(match self.node_type {
            NodeType::Leaf => LEAF_NODE_TYPE,
            NodeType::Internal => INTERNAL_NODE_TYPE,
        });
        buf.extend_from_slice(&(self.keys.len() as u16).to_le_bytes());

        // Add a null overflow address. This might get overwritten later in case the node
        // does overflow.
        buf.extend_from_slice(&[0; 8]);

        // Load all the values. This is necessary so that we don't overwrite referenced
        // values when writing the entries to the node.
        let memory = allocator.memory();
        for i in 0..self.keys.len() {
            self.value(i, memory);
        }

        // Write the children
        for child in self.children.iter() {
            buf.extend_from_slice(&child.get().to_le_bytes());
        }

        // Write the keys.
        for key in self.keys.iter() {
            // Write the size of the key.
            let key_bytes = key.to_bytes();
            buf.extend_from_slice(&(key_bytes.len() as u32).to_le_bytes());

            // Write the key.
            buf.extend_from_slice(key_bytes.borrow());
        }

        // Write the values.
        for idx in 0..self.entries_len() {
            // Write the size of the value.
            let value = self.value(idx, memory);
            buf.extend_from_slice(&(value.len() as u32).to_le_bytes());

            // Write the value.
            buf.extend_from_slice(&value);
        }

        self.write_paginated(buf, allocator, page_size as usize);
    }

    // Writes a buffer into pages of the given page size.
    // Pages can be allocated and deallocated as needed.
    fn write_paginated<M: Memory>(
        &self,
        buf: Vec<u8>,
        allocator: &mut Allocator<M>,
        page_size: usize,
    ) {
        // Compute how many overflow pages are needed.
        let additional_pages_needed = if buf.len() > page_size {
            debug_assert!(page_size >= PAGE_OVERFLOW_DATA_OFFSET.into());
            let overflow_page_capacity = page_size - PAGE_OVERFLOW_DATA_OFFSET.get() as usize;
            let overflow_data_len = buf.len() - page_size;

            // Ceiling division
            (overflow_data_len + overflow_page_capacity - 1) / overflow_page_capacity
        } else {
            0
        };

        // Retrieve the addresses for the overflow pages, making the necessary allocations.
        let overflow_addresses = self.reallocate_overflow_pages(additional_pages_needed, allocator);

        // Write the first page
        let memory = allocator.memory();
        memory.write(self.address.get(), &buf[..min(page_size, buf.len())]);
        if !overflow_addresses.is_empty() {
            // Write the next overflow address to the first page.
            write_u64(
                memory,
                self.address + OVERFLOW_ADDRESS_OFFSET,
                overflow_addresses[0].get(),
            );
        }

        // Write the overflow pages.
        let mut i = 0;
        let capacity = page_size - PAGE_OVERFLOW_DATA_OFFSET.get() as usize;
        loop {
            // Write the data from the buffer
            let start_idx = page_size + i * capacity;
            let end_idx = min(buf.len(), page_size + (i + 1) * capacity);

            if start_idx >= end_idx {
                break;
            }

            // Write magic and next address
            memory.write(overflow_addresses[i].get(), &OVERFLOW_MAGIC[..]);
            let next_address = overflow_addresses.get(i + 1).unwrap_or(&NULL);
            write_u64(
                memory,
                overflow_addresses[i] + PAGE_OVERFLOW_NEXT_OFFSET,
                next_address.get(),
            );

            // Write the overflow page contents
            memory.write(
                (overflow_addresses[i] + PAGE_OVERFLOW_DATA_OFFSET).get(),
                &buf[start_idx..end_idx],
            );

            i += 1;
        }
    }

    fn reallocate_overflow_pages<M: Memory>(
        &self,
        num_overflow_pages: usize,
        allocator: &mut Allocator<M>,
    ) -> Vec<Address> {
        // Fetch the overflow page addresses of this node.
        let mut addresses = self.get_overflow_addresses(allocator.memory());

        // If there are too many overflow addresses, deallocate some until we've reached
        // the number we need.
        while addresses.len() > num_overflow_pages {
            allocator.deallocate(addresses.pop().unwrap());
        }

        // Allocate more pages to accommodate the number requested, if needed.
        while addresses.len() < num_overflow_pages {
            addresses.push(allocator.allocate());
        }

        addresses
    }

    fn get_overflow_addresses<M: Memory>(&self, memory: &M) -> Vec<Address> {
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
fn read_node<M: Memory>(address: Address, page_size: u32, memory: &M) -> Vec<u8> {
    // Read the first page of the node.
    let mut buf = vec![0; page_size as usize];
    memory.read(address.get(), &mut buf);

    // Append overflow pages, if any.
    let mut overflow_address = address_from_slice(&buf, OVERFLOW_ADDRESS_OFFSET);
    while overflow_address != NULL {
        // Read the overflow.
        let mut overflow_buf = vec![0; page_size as usize];
        memory.read(overflow_address.get(), &mut overflow_buf);

        // Validate the magic of the overflow.
        assert_eq!(&overflow_buf[0..3], OVERFLOW_MAGIC, "Bad overflow magic.");

        // Read the next address
        overflow_address = address_from_slice(&overflow_buf, PAGE_OVERFLOW_NEXT_OFFSET);

        // Append its data to the buffer.
        buf.extend_from_slice(&overflow_buf[PAGE_OVERFLOW_DATA_OFFSET.get() as usize..]);
    }

    buf
}

fn read_u16_from_slice(slice: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes(
        (&slice[offset..offset + 2])
            .try_into()
            .expect("unable to read u16 from slice"),
    )
}

fn read_u64_from_slice(slice: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(
        (&slice[offset..offset + 8])
            .try_into()
            .expect("unable to read u64 from slice"),
    )
}

fn read_u32_from_slice(slice: &[u8], offset: Bytes) -> u32 {
    u32::from_le_bytes(
        (&slice[offset.get() as usize..offset.get() as usize + 4])
            .try_into()
            .expect("unable to read u32 from slice"),
    )
}

fn address_from_slice(slice: &[u8], offset: Bytes) -> Address {
    Address::from(read_u64_from_slice(slice, offset.get() as usize))
}
