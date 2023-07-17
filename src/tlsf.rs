//! TLSF (Two-Level Segregated Free List) Allocator
//!
//! This is a dynamic memory allocator that's constant time and provides reasonable fragmentation
//! bounds.
//!
//! Benefits:
//! * O(1) allocation and deallocation
//! * Same strategy for all block sizes

use crate::{
    read_struct,
    types::{Address, Bytes},
    write_struct, Memory,
};
use std::cmp::Ordering;

mod block;
use block::{Block, FreeBlock, TempFreeBlock, UsedBlock};

#[cfg(test)]
mod tests;

#[cfg(test)]
mod verification;

const MAGIC: &[u8; 3] = b"BTA"; // btree allocator
const LAYOUT_VERSION: u8 = 1;

// The allocator is designed to handle up 4TiB of memory.
const MEMORY_POOL_BITS: u64 = 42;

const FIRST_LEVEL_INDEX_SIZE: usize = 42;
const SECOND_LEVEL_INDEX_LOG_SIZE: usize = 5;
const SECOND_LEVEL_INDEX_SIZE: usize = 1 << SECOND_LEVEL_INDEX_LOG_SIZE;

const FOUR_TIBS: u64 = 1 << MEMORY_POOL_BITS;
const MEMORY_POOL_SIZE: u64 = FOUR_TIBS - 1;

// TODO: make this related to block header sizes?
const MINIMUM_BLOCK_SIZE: u64 = 35;

/// # Memory Layout
///
/// ```text
/// -------------------------------------------------- <- Address 0
/// Magic "BTA"                           ↕ 3 bytes
/// --------------------------------------------------
/// Layout version                        ↕ 1 byte
/// --------------------------------------------------
/// TODO: FL bitmap.                      ↕ 8 bytes    // TODO: potentially 4?
/// --------------------------------------------------
/// TODO: SL bitmap.                      ↕ 8 bytes    // TODO: potentially 4?
/// -------------------------------------------------- <- Address 20
/// Free Lists...
/// --------------------------------------------------
/// TODO: Beginning of data.
/// -------------------------------------------------- <- Page 1 (TODO: make this tighter)
/// ```
pub struct TlsfAllocator<M: Memory> {
    // The address in memory where the `TlsfHeader` is stored.
    header_addr: Address,

    //   first_level_index: u32,
    //    second_level_index: u32,

    // TODO: remove the unneeded bits from this list.
    // TODO: introduce bitmaps to make searches efficient.
    free_lists: [[Address; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],

    memory: M,
}

#[repr(C, packed)]
struct TlsfHeader {
    magic: [u8; 3],
    version: u8,
    free_lists: [[Address; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
}

impl TlsfHeader {
    pub const fn size() -> Bytes {
        Bytes::new(core::mem::size_of::<TlsfHeader>() as u64)
    }
}

impl<M: Memory> TlsfAllocator<M> {
    // Initialize.
    pub fn new(memory: M, header_addr: Address) -> Self {
        let mut tlsf = Self {
            header_addr,
            free_lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
            memory,
        };

        // Create a block with the memory.
        let mut block = FreeBlock::genesis(tlsf.data_offset());

        let (f, s) = mapping(block.size());
        block.save(&tlsf.memory);
        tlsf.free_lists[f][s] = block.address;
        tlsf.save();

        tlsf
    }

    /// Load an allocator from memory at the given `addr`.
    pub fn load(memory: M, addr: Address) -> Self {
        let header: TlsfHeader = read_struct(addr, &memory);

        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        assert_eq!(header.version, LAYOUT_VERSION, "Unsupported version.");

        Self {
            header_addr: addr,
            free_lists: header.free_lists,
            memory,
        }
    }

    /// Complexity: O(1)
    /// TODO: need to return some object that includes the length, not just the address.
    /// TODO: support allocating sizes < 32 bytes?
    //   #[cfg(test)]
    //    #[invariant(self.check_free_lists_invariant())]
    pub fn allocate(&mut self, size: u32) -> Address {
        // Adjust the size to accommodate the block header.
        let size = size + UsedBlock::header_size() as u32;

        // TODO: is this necessary?
        let size = std::cmp::max(size, MINIMUM_BLOCK_SIZE as u32);

        let block = self.search_suitable_block(size);

        // Remove the block from its free list.
        let mut block = self.remove(block);

        if block.size > size as u64 {
            // Block is bigger than the requested size. Split it if possible.
            let remaining_size = block.size - size as u64;
            if remaining_size >= MINIMUM_BLOCK_SIZE {
                block.size = size as u64;

                // Split the block
                let remaining_block = TempFreeBlock {
                    address: block.address + size.into(),
                    size: remaining_size,
                    prev_physical: block.address,
                };

                self.insert(remaining_block);
            }
        }

        // Mark the block as allocated.
        let allocated_block = block.allocate();
        allocated_block.save(&self.memory);

        self.save(); // TODO: could this be done more efficiently?

        allocated_block.address + Bytes::from(UsedBlock::header_size())
    }

    /// Deallocates a previously allocated block.
    ///
    /// PRECONDITION:
    ///   * `address` points to an allocated block.
    ///
    /// POSTCONDITION:
    ///   * The block with `address` is freed, and merged with its neighbouring free blocks.
    ///   TODO: explore how to make this more precise and add programmatic checks.
    // #[cfg(test)]
    //#[invariant(self.check_free_lists_invariant())]
    pub fn deallocate(&mut self, address: Address) {
        let address = address - Bytes::from(UsedBlock::header_size());
        let block = UsedBlock::load(address, &self.memory);

        // Free the block.
        let block = self.insert(block.deallocate());

        self.merge(block);

        self.save(); // TODO: is this necessary? I think yes. Need to write a test that detects this not being there.

        // TODO: should insertion be another explicit step?
    }

    /// Saves the allocator to memory.
    pub fn save(&self) {
        write_struct(
            &TlsfHeader {
                magic: *MAGIC,
                version: LAYOUT_VERSION,
                free_lists: self.free_lists,
            },
            self.header_addr,
            &self.memory,
        );
    }

    // Removes a free block from the free lists.
    //
    // Postconditions:
    // * block->next->prev = block->prev;
    // * block->prev->next = block->next;
    // * free list head is updated.
    fn remove(&mut self, block: FreeBlock) -> TempFreeBlock {
        match block.get_prev_free_block(&self.memory) {
            None => {
                // `block` is the head of the free list.
                let (f, s) = mapping(block.size());
                debug_assert_eq!(block.address, self.free_lists[f][s]);
                debug_assert_eq!(block.prev_free, Address::NULL);

                self.free_lists[f][s] = block.next_free;
            }
            Some(mut prev_free_block) => {
                prev_free_block.next_free = block.next_free;
                prev_free_block.save(&self.memory);
            }
        }

        match block.get_next_free_block(&self.memory) {
            None => {
                // `block` is the tail of the free list. Nothing to do.
            }
            Some(mut next_free_block) => {
                next_free_block.prev_free = block.prev_free;
                next_free_block.save(&self.memory);
            }
        }

        TempFreeBlock {
            address: block.address,
            prev_physical: block.prev_physical,
            size: block.size(),
        }
    }

    // Inserts a block into the free lists.
    //
    // Preconditions:
    //  TODO
    //
    // Postconditions:
    //  TODO
    //
    // Invariants?
    fn insert(&mut self, block: TempFreeBlock) -> FreeBlock {
        //    debug_assert!(!block.allocated);
        //
        let (f, s) = mapping(block.size);

        let mut block = block.into_free_block(self.free_lists[f][s]);

        match block.next_free {
            Address::NULL => {}
            next_free => {
                let mut next_block = FreeBlock::load(next_free, &self.memory);
                debug_assert_eq!(next_block.prev_free, Address::NULL);
                //      debug_assert!(!next_block.allocated);
                next_block.prev_free = block.address;

                next_block.save(&self.memory);
            }
        };

        //debug_assert_eq!(block.prev_free, Address::NULL);
        self.free_lists[f][s] = block.address;
        block.save(&self.memory);
        block
    }

    // Merges two free blocks that are physically adjacent to each other.
    fn merge_helper(&mut self, a: FreeBlock, b: FreeBlock) -> FreeBlock {
        // Precondition: `a` and `b` are physically adjacent to each other.
        assert_eq!(b.prev_physical, a.address);
        assert_eq!(a.address + Bytes::from(a.size()), b.address);

        // Remove them from the free lists.
        let a = self.remove(a);
        let b = FreeBlock::load(b.address, &self.memory);
        let b = self.remove(b);

        // Reload them with new pointers.
        // TODO: load them as orphaned blocks
        let a = FreeBlock::load(a.address, &self.memory);
        let b = FreeBlock::load(b.address, &self.memory);

        if let Some(mut next_block) = b.get_next_physical_block(&self.memory, self.data_offset()) {
            next_block.set_prev_physical(a.address);
            next_block.save(&self.memory);
        }

        self.insert(TempFreeBlock {
            address: a.address,
            prev_physical: a.prev_physical,
            size: a.size() + b.size(),
        })
    }

    // Merges a block with its previous and next blocks if they are free.
    // The free lists are updated accordingly.
    fn merge(&mut self, block: FreeBlock) -> FreeBlock {
        match (
            block.get_prev_physical_block(&self.memory),
            block.get_next_physical_block(&self.memory, self.data_offset()),
        ) {
            (None, None)
            | (Some(Block::Used(_)), None)
            | (None, Some(Block::Used(_)))
            | (Some(Block::Used(_)), Some(Block::Used(_))) => {
                // There are no neighbouring free physical blocks. Nothing to do.
                block
            }
            (Some(Block::Free(prev_block)), None)
            | (Some(Block::Free(prev_block)), Some(Block::Used(_))) => {
                self.merge_helper(prev_block, block)
            }
            (Some(Block::Free(prev_block)), Some(Block::Free(mut next_block))) => {
                let mut big_block = self.merge_helper(prev_block, block);

                // Reload next block.
                next_block = FreeBlock::load(next_block.address, &self.memory);
                big_block = self.merge_helper(big_block, next_block);
                big_block
            }
            (Some(Block::Used(_)), Some(Block::Free(next_block)))
            | (None, Some(Block::Free(next_block))) => self.merge_helper(block, next_block),
        }
    }

    // Returns the smallest block that accommodates the size.
    //
    // XXX: This can be done with clever bit manipulation, but we can do it the
    // naive way for a V0.
    fn search_suitable_block(&self, size: u32) -> FreeBlock {
        // Identify the free list to take blocks from.
        let (fl, sl) = mapping(size as u64);

        // Find the smallest free block that is larger than the requested size.
        for f in fl..FIRST_LEVEL_INDEX_SIZE {
            for s in sl..SECOND_LEVEL_INDEX_SIZE {
                if self.free_lists[f][s] != Address::NULL {
                    let block = FreeBlock::load(self.free_lists[f][s], &self.memory);

                    // The block must be:
                    // (1) The head of its free list.
                    debug_assert_eq!(block.prev_free, Address::NULL);
                    // (2) Free
                    //debug_assert!(!block.allocated);
                    // (3) Big enough
                    debug_assert!(block.size() >= size as u64);

                    return block;
                }
            }
        }

        panic!("OOM");
    }

    fn data_offset(&self) -> Address {
        self.header_addr + TlsfHeader::size()
    }

    /// Destroys the allocator and returns the underlying memory.
    #[inline]
    pub fn into_memory(self) -> M {
        self.memory
    }

    /// Returns a reference to the underlying memory.
    #[inline]
    pub fn memory(&self) -> &M {
        &self.memory
    }
}

// Returns the indexes that point to the corresponding segregated list.
fn mapping(size: u64) -> (usize, usize) {
    assert!(size <= MEMORY_POOL_SIZE);

    let f = u64::BITS - size.leading_zeros() - 1;
    let s = (size ^ (1 << f)) >> (f - SECOND_LEVEL_INDEX_LOG_SIZE as u32);
    (f as usize, s as usize)
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn mapping_test() {
        proptest!(|(
            size in 0..u32::MAX,
        )| {
            let (f, s) = mapping(size as u64);
            assert!((1 << f) + (((1 << f) / SECOND_LEVEL_INDEX_SIZE) * (s + 1) - 1) >= size as usize);
            if s > 0 {
                assert!((1 << f) + ((1 << f) / SECOND_LEVEL_INDEX_SIZE) * s < size as usize);
            }
        });
    }

    #[test]
    fn two_allocate() {
        let mem = make_memory();
        let mut tlsf = TlsfAllocator::new(mem, Address::from(0));
        let block_1 = tlsf.allocate(1232);

        let block_2 = tlsf.allocate(45);

        let block_3 = tlsf.allocate(39);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            tlsf.data_offset()
                + Bytes::from(1232u64)
                + Bytes::from(UsedBlock::header_size())
                + Bytes::from(45u64)
                + Bytes::from(UsedBlock::header_size())
                + Bytes::from(39u64)
                + Bytes::from(UsedBlock::header_size())
        );

        tlsf.deallocate(block_3);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            tlsf.data_offset()
                + Bytes::from(1232u64)
                + Bytes::from(UsedBlock::header_size())
                + Bytes::from(45u64)
                + Bytes::from(UsedBlock::header_size())
        );

        tlsf.deallocate(block_2);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            tlsf.data_offset() + Bytes::from(1232u64) + Bytes::from(UsedBlock::header_size())
        );

        tlsf.deallocate(block_1);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            tlsf.data_offset()
        );
    }
}
