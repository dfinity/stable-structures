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

#[derive(Debug, PartialEq)]
struct FreeLists {
    first_level_index: u64,
    second_level_index: [u32; FIRST_LEVEL_INDEX_SIZE],
    // TODO: remove the unneeded bits from this list.
    lists: [[Address; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
}

impl FreeLists {
    fn set(&mut self, f: usize, s: usize, address: Address) {
        if address == Address::NULL {
            // Unset the bit in the map.
            self.first_level_index &= !(1 << f as u64);
            self.second_level_index[f] &= !(1 << s as u32);
        } else {
            // Set the bit in the map.
            self.first_level_index |= 1 << f as u64;
            self.second_level_index[f] |= 1 << s as u64;
        }

        self.lists[f][s] = address;
    }

    fn get(&self, f: usize, s: usize) -> Address {
        self.lists[f][s]
    }
}

#[test]
fn free_lists_test() {
    let mut fl = FreeLists {
        first_level_index: 0,
        second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
        lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
    };

    fl.set(0, 0, Address::new(1));
    assert_eq!(fl.first_level_index, 1);
    assert_eq!(fl.second_level_index[0], 1);
    assert_eq!(fl.lists[0][0], Address::new(1));

    fl.set(0, 0, Address::NULL);
    assert_eq!(fl.first_level_index, 0);
    assert_eq!(fl.second_level_index[0], 0);
    assert_eq!(fl.lists[0][0], Address::NULL);

    let mut fl = FreeLists {
        first_level_index: 0,
        second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
        lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
    };

    fl.set(1, 1, Address::new(1));
    assert_eq!(fl.first_level_index, 2);
    assert_eq!(fl.second_level_index[1], 2);
    assert_eq!(fl.lists[1][1], Address::new(1));

    let mut fl = FreeLists {
        first_level_index: 0,
        second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
        lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
    };

    fl.set(16, 16, Address::new(1));
    assert_eq!(fl.first_level_index, 1 << 16);
    assert_eq!(fl.second_level_index[16], 1 << 16);
    assert_eq!(fl.lists[16][16], Address::new(1));

    fl.set(16, 31, Address::new(1));
    assert_eq!(fl.first_level_index, 1 << 16);
    assert_eq!(fl.second_level_index[16], (1 << 31) | (1 << 16));
    assert_eq!(fl.lists[16][31], Address::new(1));
}

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
    address: Address,

    internal_fragmentation: u64,

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

    internal_fragmentation: u64,
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
            internal_fragmentation: 9,
            free_lists: FreeLists {
                first_level_index: 0,
                second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
                lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
            },
            memory,
        };

        // Create a block with the memory.
        let mut block = FreeBlock::genesis(tlsf.data_offset());

        let (f, s) = mapping(block.size());
        block.save(&tlsf.memory);
        tlsf.free_lists.set(f, s, block.address);
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
            internal_fragmentation: header.internal_fragmentation,
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
    pub fn allocate(&mut self, size: u32) -> Address {
        #[cfg(test)]
        self.check_invariants();

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

        self.save();

        #[cfg(test)]
        self.check_invariants();

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

        self.save(); // TODO: is this necessary? I think yes. Need to write a test that detects this not being there.
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
                internal_fragmentation: self.internal_fragmentation,
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
    fn remove(&mut self, block: FreeBlock) -> TempFreeBlock {
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

        TempFreeBlock {
            address: block.address,
            prev_physical: block.prev_physical,
            size: block.size(),
        }
    }

    // Inserts a block into the free lists.
    fn insert(&mut self, block: TempFreeBlock) -> FreeBlock {
        let (f, s) = mapping(block.size);

        let mut block = block.into_free_block(self.free_lists.get(f, s));

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
        fn get_least_significant_bit_after(num: u32, position: usize) -> usize {
            (num & (u32::MAX - position as u32)).trailing_zeros() as usize
        }

        fn get_least_significant_bit_after_u64(num: u64, position: usize) -> usize {
            (num & (u64::MAX - position as u64)).trailing_zeros() as usize
        }

        // Identify the free list to take blocks from.
        let (f_idx, s_idx) = mapping(size as u64);

        // The identified free list maybe not have any free blocks.
        let (f, s) = {
            let s =
                get_least_significant_bit_after(self.free_lists.second_level_index[f_idx], s_idx);

            if s < u32::BITS as usize {
                (f_idx, s)
            } else {
                // Continue searching elsewhere.
                let f = get_least_significant_bit_after_u64(
                    self.free_lists.first_level_index,
                    f_idx + 1,
                );

                let s = get_least_significant_bit_after(
                    self.free_lists.second_level_index[f],
                    // s_idx + 1, // FIXME: add test case to detect this
                    0,
                );
                (f, s)
            }
        };

        if self.free_lists.get(f, s) == Address::NULL {
            panic!("Out of memory.");
        }

        let block = FreeBlock::load(self.free_lists.get(f, s), &self.memory);

        // The block must be the head of its free list and big enough.
        debug_assert_eq!(block.prev_free, Address::NULL);
        debug_assert!(block.size() >= size as u64);

        block
    }

    /*
        // Find the smallest free block that is larger than the requested size.
        for f in fl..FIRST_LEVEL_INDEX_SIZE {
            for s in sl..SECOND_LEVEL_INDEX_SIZE {
                if self.free_lists.get(f, s) != Address::NULL {
                    println!("found seglist {:?}", (f, s));
                    println!("original mapping {:?}", (fl, sl));
                    let maybe_s = (self.free_lists.second_level_index[f]
                        & (u64::MAX - (0 << sl)).leading_zeros())
                        as usize;
                    if self.free_lists.get(f, maybe_s) != Address::NULL {
                        assert_eq!(s, maybe_s);
                    } else {
                        // Continue searching elsewhere.
                        println!("FLI: {:#064b}", self.free_lists.first_level_index);
                        let new_f = (self.free_lists.first_level_index
                            & (u64::MAX - (fl as u64 + 1)))
                            .trailing_zeros() as usize;
                        println!("new f: {:?}", new_f);

                        let new_s = (self.free_lists.second_level_index[new_f]
                            & (u32::MAX - (sl as u32 + 1)))
                            .trailing_zeros() as usize;

                        assert_eq!(f, new_f);
                        assert_eq!(s, new_s);

                        //let new_s = (self.free_lists.second_level_index
                        //    & (u64::MAX - (0 << sl)).leading_zeros())
                        //    as usize;
                    }

                    let block = FreeBlock::load(self.free_lists.get(f, s), &self.memory);

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
    }*/

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
            tlsf.free_lists.get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
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
            tlsf.free_lists
                .get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
            tlsf.data_offset()
                + Bytes::from(1232u64)
                + Bytes::from(UsedBlock::header_size())
                + Bytes::from(45u64)
                + Bytes::from(UsedBlock::header_size())
        );

        tlsf.deallocate(block_2);

        assert_eq!(
            tlsf.free_lists
                .get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
            tlsf.data_offset() + Bytes::from(1232u64) + Bytes::from(UsedBlock::header_size())
        );

        tlsf.deallocate(block_1);

        assert_eq!(
            tlsf.free_lists
                .get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
            tlsf.data_offset()
        );
    }
}
