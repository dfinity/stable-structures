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
use crate::{btreemap::node::io::NodeWriter, types::NULL};

// Initial page
pub(super) const OVERFLOW_ADDRESS_OFFSET: Bytes = Bytes::new(7);
const ENTRIES_OFFSET: Bytes = Bytes::new(15);

// Overflow page
pub(super) const OVERFLOW_MAGIC: &[u8; 3] = b"NOF";
pub(super) const PAGE_OVERFLOW_NEXT_OFFSET: Bytes = Bytes::new(3);
pub(super) const PAGE_OVERFLOW_DATA_OFFSET: Bytes = Bytes::new(11);

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
            keys_and_encoded_values: vec![],
            children: vec![],
            overflows: Vec::with_capacity(0),
        }
    }

    /// Loads a v2 node from memory at the given address.
    pub(super) fn load_v2<M: Memory>(
        address: Address,
        page_size: PageSize,
        header: NodeHeader,
        memory: &M,
    ) -> Self {
        #[cfg(feature = "canbench")]
        let _p = canbench::profile("node_load_v2");

        // Load the node, including any overflows, into a buffer.
        let overflows = read_overflows(address, memory);

        let reader = NodeReader {
            address,
            overflows: &overflows,
            page_size,
            memory,
        };

        let mut offset = Address::from(0);

        // Load the node type.
        let node_type = match header.node_type {
            LEAF_NODE_TYPE => NodeType::Leaf,
            INTERNAL_NODE_TYPE => NodeType::Internal,
            other => unreachable!("Unknown node type {}", other),
        };

        // Load the number of entries
        let num_entries = header.num_entries as usize;

        // Load children if this is an internal node.
        offset += ENTRIES_OFFSET;
        let mut children = vec![];
        if node_type == NodeType::Internal {
            // The number of children is equal to the number of entries + 1.
            children.reserve_exact(num_entries + 1);
            for _ in 0..num_entries + 1 {
                let child = Address::from(read_u64(&reader, offset));
                offset += Address::size();
                children.push(child);
            }
        }

        // Load the keys.
        let mut keys_encoded_values = Vec::with_capacity(num_entries);
        let mut buf = vec![];
        for _ in 0..num_entries {
            // Load the key's size.
            let key_size = if K::BOUND.is_fixed_size() {
                // Key is fixed in size. The size of the key is always its max size.
                K::BOUND.max_size()
            } else {
                // Key is not fixed in size. Read the size from memory.
                let value = read_u32(&reader, offset);
                offset += U32_SIZE;
                value
            };

            // Load the key.
            read_to_vec(&reader, offset, &mut buf, key_size as usize);
            let key = K::from_bytes(Cow::Borrowed(&buf));
            offset += Bytes::from(key_size);
            keys_encoded_values.push((key, Value::by_ref(Bytes::from(0usize))));
        }

        // Load the values
        for (_key, value) in keys_encoded_values.iter_mut() {
            // Load the values lazily.
            *value = Value::by_ref(Bytes::from(offset.get()));
            let value_size = read_u32(&reader, offset) as usize;
            offset += U32_SIZE + Bytes::from(value_size as u64);
        }

        Self {
            address,
            keys_and_encoded_values: keys_encoded_values,
            children,
            node_type,
            version: Version::V2(page_size),
            overflows,
        }
    }

    // Saves the node to memory.
    pub(super) fn save_v2<M: Memory>(&mut self, allocator: &mut Allocator<M>) {
        #[cfg(feature = "canbench")]
        let _p = canbench::profile("node_save_v2");

        let page_size = self.version.page_size().get();
        assert!(page_size >= MINIMUM_PAGE_SIZE);

        // Load all the values. This is necessary so that we don't overwrite referenced
        // values when writing the entries to the node.
        for i in 0..self.keys_and_encoded_values.len() {
            self.value(i, allocator.memory());
        }

        // Initialize a NodeWriter. The NodeWriter takes care of allocating/deallocating
        // overflow pages as needed.
        let mut writer = NodeWriter::new(
            self.address,
            self.overflows.clone(),
            self.page_size(),
            allocator,
        );

        // Write the header of the initial page.
        let mut offset = Address::from(0);
        let header = NodeHeader {
            magic: *MAGIC,
            version: LAYOUT_VERSION_2,
            node_type: match self.node_type {
                NodeType::Leaf => LEAF_NODE_TYPE,
                NodeType::Internal => INTERNAL_NODE_TYPE,
            },
            num_entries: self.keys_and_encoded_values.len() as u16,
        };

        writer.write_struct(&header, offset);
        offset += NodeHeader::size();

        // Add a null overflow address.
        // This might get overwritten later in case the node does overflow.
        writer.write_u64(offset, self.overflows.first().unwrap_or(&NULL).get());
        offset += Bytes::from(8u64);

        // Write the children
        for child in self.children.iter() {
            writer.write_u64(offset, child.get());
            offset += Address::size();
        }

        // Write the keys.
        for (key, _) in self.keys_and_encoded_values.iter() {
            let key_bytes = key.to_bytes_checked();

            // Write the size of the key if it isn't fixed in size.
            if !K::BOUND.is_fixed_size() {
                writer.write_u32(offset, key_bytes.len() as u32);
                offset += U32_SIZE;
            }

            // Write the key.
            writer.write(offset, key_bytes.borrow());
            offset += Bytes::from(key_bytes.len());
        }

        // Write the values.
        for idx in 0..self.entries_len() {
            // Write the size of the value.
            let value = self.value(idx, writer.memory());
            writer.write_u32(offset, value.len() as u32);
            offset += U32_SIZE;

            // Write the value.
            writer.write(offset, value);
            offset += Bytes::from(value.len());
        }

        self.overflows = writer.finish();
    }
}

fn read_overflows<M: Memory>(address: Address, memory: &M) -> Vec<Address> {
    #[repr(C, packed)]
    struct OverflowPageHeader {
        magic: [u8; 3],
        next: Address,
    }

    let mut overflows = vec![];
    let mut overflow = Address::from(read_u64(memory, address + OVERFLOW_ADDRESS_OFFSET));
    while overflow != NULL {
        overflows.push(overflow);

        let header: OverflowPageHeader = read_struct(overflow, memory);
        assert_eq!(&header.magic, OVERFLOW_MAGIC, "Bad overflow magic.");
        overflow = header.next;
    }

    overflows
}
