use crate::{
    read_struct,
    types::{Address, Bytes},
    write_struct, Memory,
};
use std::cmp::Ordering;

mod block;
use block::{Block, FreeBlock, TransFreeBlock, UsedBlock};
mod free_lists;
use free_lists::{mapping, FreeLists};
#[cfg(test)]
mod tests;
#[cfg(test)]
mod verification;

const MAGIC: &[u8; 3] = b"TLS"; // "Two-Level Segregated Free List"
const LAYOUT_VERSION: u8 = 1;

// The allocator is designed to handle up 4TiB of memory.
const MEMORY_POOL_BITS: u64 = 42;

const FIRST_LEVEL_INDEX_SIZE: usize = 42;
const SECOND_LEVEL_INDEX_LOG_SIZE: usize = 5;
const SECOND_LEVEL_INDEX_SIZE: usize = 1 << SECOND_LEVEL_INDEX_LOG_SIZE;
const FOUR_TIBS: u64 = 1 << MEMORY_POOL_BITS;
const MEMORY_POOL_SIZE: u64 = FOUR_TIBS - 1;

// The minimum size of a block must fit the free block header.
const MINIMUM_BLOCK_SIZE: u64 = FreeBlock::header_size();

/// A Two-Level Segregated Free List (TLSF) Allocator
///
/// TLSF is a dynamic memory allocator. Given a `Memory`, it provides an API to allocate/deallocate
/// blocks of memory of arbitrary size.
///
/// This implementation is based on the following paper:
///
/// "TLSF: a New Dynamic Memory Allocator for Real-Time Systems" by Masmano et al.
/// http://www.gii.upv.es/tlsf/files/ecrts04_tlsf.pdf
///
/// TLSF tracks free and used memory in "blocks". Initially, the TLSF allocator considers the
/// entire memory to be one big free block, and as allocations happen this block into is split
/// into smaller blocks.
///
/// In order to find free blocks efficiently, TLSF uses linked lists to track blocks of different
/// sizes. For example, there can be a linked list tracking containing all the free blocks that are
/// 33-35 bytes in size, or 120-127 bytes in size, etc. This approach is referred to as "segregated
/// free lists".
///
/// The more segregated free lists there are, the quicker it is to find a block that is a "good
/// fit". In the extreme case, there can be a segregated free list for every possible size. The
/// downside of having too many segregated free lists, on the other hand, is that it becomes slower
/// to find blocks (Best fit).
///
/// TODO: add example that explains this.
///
/// TLSF allows us to manage a large number of segregated free lists to reduce fragmentation, while
/// keeping the runtime complexity of `allocate` and `deallocate` at O(1).
///
/// TODO: add diagram for TLSF structure
///
/// # Memory Layout
///
/// ```text
/// -------------------------------------------------- <- Address 0
/// Magic                                 ↕ 3 bytes
/// --------------------------------------------------
/// Layout version                        ↕ 1 byte
/// --------------------------------------------------
/// First level bitmap                    ↕ 8 bytes
/// --------------------------------------------------
/// Second level bitmaps                  ↕ 4 * (FIRST_LEVEL_INDEX_SIZE) bytes
/// --------------------------------------------------
/// Free lists                            ↕ 8 * SECOND_LEVEL_INDEX_SIZE * FIRST_LEVEL_INDEX_SIZE
/// --------------------------------------------------
/// TODO: reserve some more space?
/// --------------------------------------------------
/// Blocks
/// --------------------------------------------------
/// ```
pub struct TlsfAllocator<M: Memory> {
    // The address in memory where the `TlsfHeader` is stored.
    address: Address,

    free_lists: FreeLists,

    memory: M,
}

#[repr(C, packed)]
struct TlsfHeader {
    magic: [u8; 3],
    version: u8,
    first_level_index: u64,
    second_level_index: [u32; FIRST_LEVEL_INDEX_SIZE],
    free_lists: [[Address; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
}

impl TlsfHeader {
    pub const fn size() -> Bytes {
        Bytes::new(core::mem::size_of::<TlsfHeader>() as u64)
    }
}

impl<M: Memory> TlsfAllocator<M> {
    /// Initialize an allocator and store it in the given `address`.
    pub fn new(memory: M, address: Address) -> Self {
        let mut tlsf = Self {
            address,
            free_lists: FreeLists {
                first_level_index: 0,
                second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
                lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
            },
            memory,
        };

        // Insert the entire memory pool as a single free block.
        tlsf.insert(TransFreeBlock {
            address: tlsf.data_offset(),
            prev_physical: Address::NULL,
            size: MEMORY_POOL_SIZE,
        });

        tlsf.save();

        tlsf
    }

    /// Load an allocator from memory at the given `address`.
    pub fn load(memory: M, address: Address) -> Self {
        let header: TlsfHeader = read_struct(address, &memory);

        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        assert_eq!(header.version, LAYOUT_VERSION, "Unsupported version.");

        Self {
            address,
            free_lists: FreeLists {
                first_level_index: header.first_level_index,
                second_level_index: header.second_level_index,
                lists: header.free_lists,
            },
            memory,
        }
    }

    /// Allocates a new chunk from memory with the given `size`.
    ///
    /// Precondition:
    ///  * A free block exists with size bigger than the requested size.
    ///
    /// Postcondition:
    ///  * A block with size >= `size` is allocated.
    ///
    /// Complexity: O(1)
    #[cfg_attr(test, invariant(self.check_invariants()))]
    pub fn allocate(&mut self, size: u32) -> Address {
        // Adjust the size to accommodate the used block header.
        let size = size + UsedBlock::header_size() as u32;

        // Size must also be >= MINIMUM_BLOCK_SIZE
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
                let remaining_block = TransFreeBlock {
                    address: block.address + size.into(),
                    size: remaining_size,
                    prev_physical: block.address,
                };

                self.insert(remaining_block);
            } else {
                // TODO: add test case for this condition.
            }
        }

        // Allocate the block.
        let allocated_block = block.allocate();
        allocated_block.save(&self.memory);

        // TODO: this can be made more efficient.
        self.save();

        allocated_block.address + Bytes::from(UsedBlock::header_size())
    }

    /// Deallocates a previously allocated block.
    ///
    /// Complexity: O(1)
    #[cfg_attr(test, requires(self.block_is_allocated(address)))]
    #[cfg_attr(test, invariant(self.check_invariants()))]
    #[cfg_attr(test, ensures(!self.block_is_allocated(address)))]
    pub fn deallocate(&mut self, address: Address) {
        let address = address - Bytes::from(UsedBlock::header_size());
        let block = UsedBlock::load(address, &self.memory);

        // Free the block.
        let block = self.insert(block.deallocate());

        self.merge(block);

        self.save(); // TODO: add test that detects this save not being there.
    }

    /// Saves the allocator to memory.
    pub fn save(&self) {
        write_struct(
            &TlsfHeader {
                magic: *MAGIC,
                version: LAYOUT_VERSION,
                first_level_index: self.free_lists.first_level_index,
                second_level_index: self.free_lists.second_level_index,
                free_lists: self.free_lists.lists,
            },
            self.address,
            &self.memory,
        );
    }

    // Removes a free block from the free lists.
    //
    // Postconditions:
    // * block->next->prev = block->prev;
    // * block->prev->next = block->next;
    // * free list head is updated.
    fn remove(&mut self, block: FreeBlock) -> TransFreeBlock {
        match block.get_prev_free_block(&self.memory) {
            None => {
                // `block` is the head of the free list.
                let (f, s) = mapping(block.size());
                debug_assert_eq!(block.address, self.free_lists.get(f, s));
                debug_assert_eq!(block.prev_free, Address::NULL);

                self.free_lists.set(f, s, block.next_free);
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

        TransFreeBlock {
            address: block.address,
            prev_physical: block.prev_physical,
            size: block.size(),
        }
    }

    // Inserts a block into the free lists.
    fn insert(&mut self, block: TransFreeBlock) -> FreeBlock {
        let (f, s) = mapping(block.size);

        let block = block.into_free_block(self.free_lists.get(f, s));

        match block.next_free {
            Address::NULL => {}
            next_free => {
                let mut next_block = FreeBlock::load(next_free, &self.memory);
                debug_assert_eq!(next_block.prev_free, Address::NULL);
                next_block.prev_free = block.address;
                next_block.save(&self.memory);
            }
        };

        self.free_lists.set(f, s, block.address);
        block.save(&self.memory);
        block
    }

    // Merges two free blocks that are physically adjacent to each other.
    fn merge_helper(&mut self, a: FreeBlock, b: FreeBlock) -> FreeBlock {
        // Precondition: `a` and `b` are physically adjacent to each other.
        assert_eq!(b.prev_physical, a.address);
        assert_eq!(a.address + Bytes::from(a.size()), b.address);

        // Remove them from the free lists.
        // TODO: look into reducing these loading blocks from memory.
        let a = self.remove(a);
        let b = FreeBlock::load(b.address, &self.memory);
        let b = self.remove(b);

        // Reload them with new pointers.
        let a = FreeBlock::load(a.address, &self.memory);
        let b = FreeBlock::load(b.address, &self.memory);

        if let Some(mut next_block) = b.get_next_physical_block(&self.memory, self.data_offset()) {
            next_block.set_prev_physical(a.address);
            next_block.save(&self.memory);
        }

        self.insert(TransFreeBlock {
            address: a.address,
            prev_physical: a.prev_physical,
            size: a.size() + b.size(),
        })
    }

    // Merges a block with its previous and next blocks if they are free.
    // The free lists are updated accordingly.
    fn merge(&mut self, block: FreeBlock) -> FreeBlock {
        // TODO: consider looping several times to reduce fragmentation.
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
    fn search_suitable_block(&self, size: u32) -> FreeBlock {
        // The identified free list maybe not have any free blocks.
        let (f, s) = self.free_lists.search(size);

        if self.free_lists.get(f, s) == Address::NULL {
            panic!("Out of memory.");
        }

        let block = FreeBlock::load(self.free_lists.get(f, s), &self.memory);

        // The block must be the head of its free list and big enough.
        debug_assert_eq!(block.prev_free, Address::NULL);
        debug_assert!(block.size() >= size as u64);

        block
    }

    fn data_offset(&self) -> Address {
        self.address + TlsfHeader::size()
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
