//! This module implements memory sizes for memory manager.
//!
//! # V1 Memory Sizes Layout
//!
//! ```text
//! -------------------------------------------------- <- Address 40 (MEMORY_SIZES_OFFSET)
//! Size of memory 0 (in pages)           ↕ 8 bytes
//! --------------------------------------------------
//! Size of memory 1 (in pages)           ↕ 8 bytes
//! --------------------------------------------------
//! ...
//! --------------------------------------------------
//! Size of memory 254 (in pages)         ↕ 8 bytes
//! -------------------------------------------------- <- Address 2080 (BUCKET_ALLOCATIONS_OFFSET)
//! ```
use crate::Memory;

use super::MemoryId;

// The maximum number of memories that can be created. Must be <= u8::MAX
pub const MAX_NUM_MEMORIES: usize = 255;

/// The offset where memory sizes begin.
const MEMORY_SIZES_OFFSET: usize = 40;
/// The size of the memory sizes.
const MEMORY_SIZES_SIZE: usize = MAX_NUM_MEMORIES * core::mem::size_of::<u64>();

/// Represents memory sizes in memory. Implements all the memory
/// operations, like `new`, `load`, `save` etc...
#[derive(Clone)]
pub struct V1 {
    // An array storing the size (in pages) of each of the managed memories.
    memory_sizes_in_pages: [u64; MAX_NUM_MEMORIES],
}

impl V1 {
    /// Creates new memory sizes instance. Note, the sizes must be explicitly
    /// saved into the memory.
    pub fn new() -> Self {
        Self {
            memory_sizes_in_pages: [0; MAX_NUM_MEMORIES],
        }
    }

    /// Saves the full header into the memory.
    pub fn save<M: Memory>(&self, memory: &M) {
        let buf = [0; MEMORY_SIZES_SIZE];
        crate::write(memory, MEMORY_SIZES_OFFSET as u64, &buf);
    }

    /// Loads the full header from the memory.
    pub fn load<M: Memory>(memory: &M) -> Self {
        let mut buf = [0; MEMORY_SIZES_SIZE];
        memory.read(MEMORY_SIZES_OFFSET as u64, &mut buf);
        Self {
            memory_sizes_in_pages: buf[..]
                .chunks(core::mem::size_of::<u64>())
                .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }

    // Returns the size of the specified memory in pages.
    pub fn size_in_pages(&self, id: MemoryId) -> u64 {
        self.memory_sizes_in_pages[id.0 as usize]
    }

    /// Save memory size in pages for the specified memory id.
    pub fn save_size_in_pages<M: Memory>(&mut self, memory: &M, id: MemoryId, new_size: u64) {
        self.memory_sizes_in_pages[id.0 as usize] = new_size;
        crate::write(
            memory,
            (MEMORY_SIZES_OFFSET + id.0 as usize * core::mem::size_of::<u64>()) as u64,
            &self.memory_sizes_in_pages[id.0 as usize].to_le_bytes(),
        );
    }
}
