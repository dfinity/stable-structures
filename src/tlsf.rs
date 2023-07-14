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

#[cfg(test)]
mod tests;

#[cfg(test)]
mod verification;

const MAGIC: &[u8; 3] = b"BTA"; // btree allocator
const LAYOUT_VERSION: u8 = 1;

const FIRST_LEVEL_INDEX_SIZE: usize = 32;
const SECOND_LEVEL_INDEX_LOG_SIZE: usize = 5;
const SECOND_LEVEL_INDEX_SIZE: usize = 1 << SECOND_LEVEL_INDEX_LOG_SIZE;

const MEMORY_POOL_SIZE: u32 = u32::MAX;

// TODO: Make this bound tighter.
const HEADER_SIZE: Bytes = Bytes::new(10_000);

//const GRANULARITY_LOG2: u32 = GRANULARITY.trailing_zeros();

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

impl<M: Memory> TlsfAllocator<M> {
    // Initialize.
    pub fn new(memory: M, header_addr: Address) -> Self {
        let mut tlsf = Self {
            header_addr,
            free_lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
            memory,
        };

        // TODO: make it span at least 1TiB.
        // Create a block with the memory.
        let block = FreeBlock {
            address: tlsf.data_offset(),
            size: MEMORY_POOL_SIZE,
            prev_free: Address::NULL,
            next_free: Address::NULL,
            prev_physical: Address::NULL,
        };

        let (f, s) = mapping(block.size);
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
    /// TODO: support allocating sizes < 3 bytes?
    //   #[cfg(test)]
    //    #[invariant(self.check_free_lists_invariant())]
    pub fn allocate(&mut self, size: u32) -> Address {
        // Adjust the size to accommodate the block header.
        let size = size + FreeBlock::header_size() as u32;

        let block = self.search_suitable_block(size);

        // Remove the block from its free list.
        let mut block = self.remove(block);

        if block.size > size {
            // Block is bigger than the requested size. Split it.
            let remaining_size = block.size - size;
            block.size = size;

            // Split the block
            let remaining_block = OrphanedFreeBlock {
                address: block.address + size.into(),
                size: remaining_size,
                prev_physical: block.address,
            };

            self.insert(remaining_block);
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
        let address = address - Bytes::from(FreeBlock::header_size());
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
    fn remove(&mut self, block: FreeBlock) -> OrphanedFreeBlock {
        // Precondition: `block` is free.
        //debug_assert!(!block.allocated);

        match block.get_prev_free_block(&self.memory) {
            None => {
                // `block` is the head of the free list.
                let (f, s) = mapping(block.size);
                debug_assert_eq!(block.address, self.free_lists[f][s]);
                debug_assert_eq!(block.prev_free, Address::NULL);

                self.free_lists[f][s] = block.next_free;

                if let Some(mut next_block) = block.get_next_free_block(&self.memory) {
                    next_block.prev_free = Address::NULL;
                    next_block.save(&self.memory);
                }
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

        OrphanedFreeBlock {
            address: block.address,
            prev_physical: block.prev_physical,
            size: block.size,
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
    fn insert(&mut self, block: OrphanedFreeBlock) -> FreeBlock {
        //    debug_assert!(!block.allocated);
        //
        let (f, s) = mapping(block.size);

        let block = FreeBlock {
            address: block.address,
            //   allocated: false,
            prev_free: Address::NULL,
            next_free: self.free_lists[f][s],
            prev_physical: block.prev_physical,
            size: block.size,
        };

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
        assert_eq!(a.address + Bytes::from(a.size), b.address);

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

        self.insert(OrphanedFreeBlock {
            address: a.address,
            prev_physical: a.prev_physical,
            size: a.size + b.size,
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
        let (fl, sl) = mapping(size);

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
                    debug_assert!(block.size >= size);

                    return block;
                }
            }
        }

        panic!("OOM");
    }

    fn data_offset(&self) -> Address {
        self.header_addr + HEADER_SIZE
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

struct UsedBlock {
    address: Address,
    prev_physical: Address,
    size: u32,
}

impl UsedBlock {
    fn deallocate(self) -> OrphanedFreeBlock {
        OrphanedFreeBlock {
            address: self.address,
            prev_physical: self.prev_physical,
            size: self.size,
        }
    }

    fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: BlockHeader = read_struct(address, memory);
        // TODO: check magic and version?
        assert!(header.allocated);
        assert_eq!(header.prev_free, Address::NULL);
        assert_eq!(header.next_free, Address::NULL);

        Self {
            address,
            size: header.size,
            prev_physical: header.prev_physical,
        }
    }

    fn save<M: Memory>(&self, memory: &M) {
        write_struct(
            &BlockHeader {
                allocated: true,
                prev_free: Address::NULL,
                next_free: Address::NULL,
                size: self.size,
                prev_physical: self.prev_physical,
            },
            self.address,
            memory,
        )
    }

    // TODO: used block headers are smaller.
    fn header_size() -> u64 {
        core::mem::size_of::<BlockHeader>() as u64
    }
}

struct OrphanedFreeBlock {
    address: Address,
    prev_physical: Address,
    size: u32,
}

impl OrphanedFreeBlock {
    fn allocate(self) -> UsedBlock {
        UsedBlock {
            address: self.address,
            prev_physical: self.prev_physical,
            size: self.size,
        }
    }

    // TODO: maybe a split method?
}

enum Block {
    Free(FreeBlock),
    Used(UsedBlock),
}

impl Block {
    fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: BlockHeader = read_struct(address, memory);

        // TODO: avoid reading the header twice.
        match header.allocated {
            false => Self::Free(FreeBlock::load(address, memory)),
            true => Self::Used(UsedBlock::load(address, memory)),
        }
    }

    // TODO: consider removing this.
    fn set_prev_physical(&mut self, prev_physical: Address) {
        match self {
            Self::Free(b) => b.prev_physical = prev_physical,
            Self::Used(b) => b.prev_physical = prev_physical,
        }
    }

    fn save<M: Memory>(&self, memory: &M) {
        match self {
            Self::Free(b) => b.save(memory),
            Self::Used(b) => b.save(memory),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct FreeBlock {
    address: Address,
    //    allocated: bool,
    prev_free: Address,
    next_free: Address,
    prev_physical: Address,

    // The size of the block, including the header.
    size: u32,
}

impl FreeBlock {
    fn save<M: Memory>(&self, memory: &M) {
        if self.next_free != Address::NULL {
            assert!(
                self.next_free < self.address
                    || self.next_free >= self.address + Bytes::from(self.size)
            );
        }

        write_struct(
            &BlockHeader {
                allocated: false,
                prev_free: self.prev_free,
                next_free: self.next_free,
                size: self.size,
                prev_physical: self.prev_physical,
            },
            self.address,
            memory,
        )
    }

    // Loads the next physical block in memory.
    // If this is the last physical block in memory, `None` is returned.
    fn get_next_physical_block<M: Memory>(
        &self,
        memory: &M,
        data_offset: Address,
    ) -> Option<Block> {
        let next_address = self.address + Bytes::from(self.size);

        let max_address = data_offset + Bytes::from(MEMORY_POOL_SIZE);

        match next_address.cmp(&max_address) {
            Ordering::Less => {
                let block = Block::load(next_address, memory);
                // TODO: bring that assertion again.
                //debug_assert_eq!(block.prev_physical, self.address);
                Some(block)
            }
            Ordering::Equal => None,
            Ordering::Greater => {
                unreachable!("out of bounds.")
            }
        }
    }

    // Loads the previous physical block in memory.
    // If this is the first physical block in memory, `None` is returned.
    fn get_prev_physical_block<M: Memory>(&self, memory: &M) -> Option<Block> {
        match self.prev_physical {
            // TODO: in prev physical is null, maybe assert that block's address is the data
            // offset?
            Address::NULL => None,
            prev_physical => Some(Block::load(prev_physical, memory)),
        }
    }

    // Loads the previous free block if it exists, `None` otherwise.
    fn get_prev_free_block<M: Memory>(&self, memory: &M) -> Option<FreeBlock> {
        if self.prev_free != Address::NULL {
            let prev_free = Self::load(self.prev_free, memory);

            // Assert that the previous block is pointing to the current block.
            debug_assert_eq!(prev_free.next_free, self.address);
            // Assert that the previous block is free.
            //debug_assert!(!prev_free.allocated);

            Some(prev_free)
        } else {
            None
        }
    }

    // Loads the next free block if it exists, `None` otherwise.
    fn get_next_free_block<M: Memory>(&self, memory: &M) -> Option<FreeBlock> {
        if self.next_free != Address::NULL {
            let next_free = Self::load(self.next_free, memory);

            // Assert that the next block is pointing to the current block.
            //debug_assert_eq!(next_free.prev_free, self.address);
            // Assert that the next block is free.
            //debug_assert!(!next_free.allocated);

            Some(next_free)
        } else {
            None
        }
    }

    fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: BlockHeader = read_struct(address, memory);
        // TODO: check magic and version?
        assert!(!header.allocated);

        Self {
            address,
            prev_free: header.prev_free,
            next_free: header.next_free,
            size: header.size,
            prev_physical: header.prev_physical,
        }
    }

    fn header_size() -> u64 {
        core::mem::size_of::<BlockHeader>() as u64
    }
}

#[derive(Debug, Copy, Clone)]
#[repr(C, packed)]
struct BlockHeader {
    allocated: bool,
    size: u32,
    prev_free: Address,
    next_free: Address,
    prev_physical: Address,
}

// Returns the indexes that point to the corresponding segregated list.
fn mapping(size: u32) -> (usize, usize) {
    let f = u32::BITS - size.leading_zeros() - 1;
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
            let (f, s) = mapping(size);
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
