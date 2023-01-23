//! This module implements a header for memory manager.
//!
//! # V1 Header Layout
//!
//! ```text
//! -------------------------------------------------- <- Address 0
//! Magic "MGR"                           ↕ 3 bytes
//! --------------------------------------------------
//! Layout version                        ↕ 1 byte
//! --------------------------------------------------
//! Number of allocated buckets           ↕ 2 bytes
//! --------------------------------------------------
//! Bucket size (in pages) = N            ↕ 2 bytes
//! -------------------------------------------------- <- Address 8 (HEADER_SIZE)
//! Reserved space                        ↕ 32 bytes
//! -------------------------------------------------- <- Address 40 (MEMORY_SIZES_OFFSET)
//! ```
use crate::Memory;

pub const MAGIC: [u8; 3] = *b"MGR";
pub const LAYOUT_VERSION: u8 = 1;
/// The size of all the header field bytes.
const HEADER_SIZE: usize = 8;

/// Represents a header in memory. Implements all the memory
/// operations, like `new`, `load`, `save` etc...
#[derive(Clone)]
pub struct V1 {
    // The number of buckets allocated by the memory manager.
    allocated_buckets: u16,
    // The size of a bucket in Wasm pages.
    bucket_size_in_pages: u16,
}

impl V1 {
    /// Creates a new header instance. Note, the header must be explicitly
    /// saved into the memory.
    pub fn new(bucket_size_in_pages: u16) -> Self {
        Self {
            allocated_buckets: Default::default(),
            bucket_size_in_pages,
        }
    }

    /// Saves the full header into the memory.
    pub fn save<M: Memory>(&self, memory: &M) {
        let mut buf = [0; HEADER_SIZE];
        buf[0..3].copy_from_slice(&MAGIC);
        buf[3] = LAYOUT_VERSION;
        buf[4..6].copy_from_slice(&self.allocated_buckets.to_le_bytes());
        buf[6..8].copy_from_slice(&self.bucket_size_in_pages.to_le_bytes());
        crate::write(memory, 0, &buf);
    }

    /// Loads the full header from the memory.
    pub fn load<M: Memory>(memory: &M) -> Self {
        let mut buf = [0; HEADER_SIZE];
        memory.read(0, &mut buf);
        let magic = &buf[0..3];
        assert_eq!(MAGIC, magic);
        let layout_version = buf[3];
        assert_eq!(LAYOUT_VERSION, layout_version);
        let allocated_buckets = u16::from_le_bytes(buf[4..6].try_into().unwrap());
        let bucket_size_in_pages = u16::from_le_bytes(buf[6..8].try_into().unwrap());

        Self {
            allocated_buckets,
            bucket_size_in_pages,
        }
    }

    /// Returns true if the header in memory is valid.
    pub fn is_valid<M: Memory>(memory: &M) -> bool {
        let mut magic = [0; 3];
        memory.read(0, &mut magic);
        magic == MAGIC
    }

    /// Returns the number of currently allocated buckets.
    pub fn allocated_buckets(&self) -> u16 {
        self.allocated_buckets
    }

    /// Sets the number of currently allocated buckets.
    pub fn save_allocated_buckets<M: Memory>(&mut self, memory: &M, allocated_buckets: u16) {
        self.allocated_buckets = allocated_buckets;
        crate::write(memory, 4, &allocated_buckets.to_le_bytes());
    }

    /// Returns the bucket size in pages.
    pub fn bucket_size_in_pages(&self) -> u16 {
        self.bucket_size_in_pages
    }
}

#[cfg(test)]
mod test {
    use crate::types::Address;
    use std::{cell::RefCell, rc::Rc};

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    #[allow(unaligned_references)]
    fn load_save_header_is_identical_to_read_write_struct() {
        #[repr(C, packed)]
        struct PackedHeader {
            magic: [u8; 3],
            version: u8,
            // The number of buckets allocated by the memory manager.
            allocated_buckets: u16,
            // The size of a bucket in Wasm pages.
            bucket_size_in_pages: u16,
            // Reserved bytes for future extensions
        }

        let packed_header = PackedHeader {
            magic: super::MAGIC,
            version: super::LAYOUT_VERSION,
            allocated_buckets: 0xDEAD,
            bucket_size_in_pages: 0xBEEF,
        };

        let packed_mem = make_memory();
        crate::write_struct(&packed_header, Address::from(0), &packed_mem);

        let v1_header = super::V1 {
            allocated_buckets: 0xDEAD,
            bucket_size_in_pages: 0xBEEF,
        };

        let v1_mem = make_memory();
        v1_header.save(&v1_mem);

        assert_eq!(packed_mem, v1_mem);

        let packed_header: PackedHeader = crate::read_struct(Address::from(0), &v1_mem);
        let v1_header = super::V1::load(&v1_mem);
        assert_eq!(packed_header.allocated_buckets, v1_header.allocated_buckets);
        assert_eq!(
            packed_header.bucket_size_in_pages,
            v1_header.bucket_size_in_pages
        );
    }
}
