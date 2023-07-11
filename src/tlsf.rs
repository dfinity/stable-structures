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
    write_struct, Memory, WASM_PAGE_SIZE,
};

// As defined in the paper.
const MINIMUM_BLOCK_SIZE: u32 = 16;

const FIRST_LEVEL_INDEX_SIZE: usize = 32;
const SECOND_LEVEL_INDEX_LOG_SIZE: usize = 5;
const SECOND_LEVEL_INDEX_SIZE: usize = 1 << SECOND_LEVEL_INDEX_LOG_SIZE;

const DATA_OFFSET: Address = Address::new(WASM_PAGE_SIZE);

const MEMORY_POOL_SIZE: u32 = u32::MAX;

struct SegList(usize, usize);

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
    //   first_level_index: u32,
    //    second_level_index: u32,

    // TODO: remove the unneeded bits from this list.
    // TODO: introduce bitmaps to make searches efficient.
    free_lists: [[Address; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],

    memory: M,
}

impl<M: Memory> TlsfAllocator<M> {
    // Initialize.
    pub fn new(memory: M) -> Self {
        let mut free_lists = [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE];

        // Create a block with the memory.
        // TODO: make it span at least 1TiB.
        let block = Block {
            address: DATA_OFFSET,
            allocated: false,
            size: MEMORY_POOL_SIZE,
            prev_free: Address::NULL,
            next_free: Address::NULL,
            prev_physical: Address::NULL,
        };

        block.save(&memory);

        free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1] = DATA_OFFSET;

        Self { free_lists, memory }
    }

    // TODO: load, init

    pub fn allocate(&mut self, size: u32) -> Address {
        let size = size + Block::header_size() as u32;
        let (fl, sl) = mapping(size);

        let block_seg_list = self.search_suitable_block(size, fl as usize, sl as usize);

        let mut block = Block::load(
            self.free_lists[block_seg_list.0][block_seg_list.1],
            &self.memory,
        );

        // Remove the block
        self.free_lists[block_seg_list.0][block_seg_list.1] = block.next_free;
        block.allocated = true;

        if block.size > size {
            let remaining_size = block.size - size;
            let (fl, sl) = mapping(remaining_size);

            // Split the block
            let remaining_block = Block {
                address: block.address + size.into(),
                allocated: false,
                prev_free: block.prev_free, // TODO: assert this to be null?
                next_free: self.free_lists[fl as usize][sl as usize],
                size: remaining_size,
                prev_physical: block.address,
            };

            block.size = size;

            // Insert the block.
            self.free_lists[fl as usize][sl as usize] = remaining_block.address;
            block.save(&self.memory);
            remaining_block.save(&self.memory);
        }

        block.address + Bytes::from(Block::header_size())
        /*
        remove (found_block); // O(1)
        if (sizeof(found_block)>size) {
        remaining_block = split (found_block, size);
        mapping (sizeof(remaining_block),&fl2,&sl2);
        insert (remaining_block, fl2, sl2); // O(1)
        }
        return found_block;*/
    }

    // Removes a free block from the free lists.
    //
    // Postconditions:
    // * block->next->prev = block->prev;
    // * block->prev->next = block->next;
    // * free list head is updated.
    fn remove(&mut self, block: &Block) {
        println!("REMOVE: {:#?}", block);
        // Precondition: `block` is free.
        debug_assert!(!block.allocated);

        match block.get_prev_free_block(&self.memory) {
            None => {
                // `block` is the head of the free list.
                //    let (f, s) = mapping(block.size);
                // NOTE: this doesn't actually need to be the case because the block has just been
                // freed
                //     debug_assert_eq!(block.address, self.free_lists[f as usize][s as usize]);
            }
            Some(mut prev_free_block) => {
                println!("updating prev block: {:?}", prev_free_block);
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
    }

    fn insert(&mut self, block: &mut Block) {
        println!("inserting block: {:?}", block);
        debug_assert!(!block.allocated);

        let (f, s) = mapping(block.size);
        block.next_free = self.free_lists[f as usize][s as usize];

        match block.next_free {
            Address::NULL => {}
            next_free => {
                let mut next_block = Block::load(next_free, &self.memory);
                debug_assert_eq!(next_block.prev_free, Address::NULL);
                debug_assert!(!next_block.allocated);
                next_block.prev_free = block.address;
                next_block.save(&self.memory);
            }
        };

        println!("adding block to {:?}", (f, s));
        self.free_lists[f as usize][s as usize] = block.address;
        block.save(&self.memory);
    }

    // Merges a block with its previous and next blocks if they are free.
    // The free lists are updated accordingly.
    fn merge(&mut self, mut block: Block) -> Block {
        println!("merging block {:?}", block);
        // Precondition: `block` is free.
        debug_assert!(!block.allocated);

        match (
            block.get_prev_physical_block(&self.memory),
            block.get_next_physical_block(&self.memory),
        ) {
            (None, None) => {
                self.remove(&block);
                return block;
            }
            (Some(mut prev_block), None) => {
                if !prev_block.allocated {
                    self.remove(&block);
                    self.remove(&prev_block);

                    prev_block.size += block.size;
                    self.insert(&mut prev_block);
                    return prev_block;
                }
                block
            }
            (Some(mut prev_block), Some(mut next_block)) => {
                println!("prev block: {:?}", prev_block);
                println!("next block: {:?}", next_block);
                if !prev_block.allocated {
                    println!("MERGE CASE 3.1");
                    self.remove(&block);
                    self.remove(&prev_block);

                    prev_block.size += block.size;

                    if !next_block.allocated {
                        self.remove(&next_block);
                        prev_block.size += next_block.size;
                    }

                    next_block.prev_physical = prev_block.address;
                    next_block.save(&self.memory);

                    self.insert(&mut prev_block);
                    return prev_block;
                } else {
                    println!("MERGE CASE 3.2");
                    if !next_block.allocated {
                        self.remove(&next_block);
                        block.size += next_block.size;

                        // Update prev physical of next next block.
                        if let Some(mut uber_next_block) =
                            next_block.get_next_physical_block(&self.memory)
                        {
                            println!("uber next block: {:#?}", uber_next_block);
                            uber_next_block.prev_physical = block.address;
                            uber_next_block.save(&self.memory);
                        }
                    }

                    self.insert(&mut block);
                    return block;
                }
            }
            (None, Some(next_block)) => {
                println!("MERGE CASE 4");
                if !next_block.allocated {
                    println!("merging next block");
                    self.remove(&next_block);
                    block.size += next_block.size;

                    // Update prev physical of next next block.
                    if let Some(mut uber_next_block) =
                        next_block.get_next_physical_block(&self.memory)
                    {
                        println!("uber next block: {:#?}", uber_next_block);
                        uber_next_block.prev_physical = block.address;
                        uber_next_block.save(&self.memory);
                    }
                }

                self.remove(&block); // TODO can/should this be moved to the if statement above?
                self.insert(&mut block);
                return block;
            }
        }
    }

    pub fn deallocate(&mut self, address: Address) {
        let address = address - Bytes::from(Block::header_size());
        let mut block = Block::load(address, &self.memory);
        println!("Deallocating block {:#?}", block);

        block.allocated = false;

        self.merge(block);

        // TODO: should insertion be another explicit step?

        /*// Check if the next physical block is free, and merge it.
        let next_block_address = block_to_remove.address + Bytes::from(block_to_remove.size);
        assert!(next_block_address <= DATA_OFFSET + Bytes::from(u32::MAX));
        if next_block_address < DATA_OFFSET + Bytes::from(u32::MAX) {
            // there's a next block. if it's empty, merge it into current block.
            let next_block = Block::load(next_block_address, &self.memory);
            if !next_block.allocated {
                // TODO: Remove next block from free lists.

                block_to_remove.size += next_block.size;

                // Update list.
            }
        }

        // Merge the previous block if it's available and free.
        if block_to_remove.prev_physical != Address::NULL {
            let mut prev_block = Block::load(block_to_remove.prev_physical, &self.memory);
            if !prev_block.allocated {
                prev_block.size += block_to_remove.size;
                prev_block.save(&self.memory);

                // TODO: remove prev block from free lists?

                let (f, s) = mapping(prev_block.size);
                prev_block.next_free = self.free_lists[f as usize][s as usize];
                self.free_lists[f as usize][s as usize] = prev_block.address;
                return;
            }
        }

        block_to_remove.allocated = false;
        block_to_remove.save(&self.memory);

        // Insert the block into free blocks.
        let (f, s) = mapping(block_to_remove.size);
        block_to_remove.next_free = self.free_lists[f as usize][s as usize];
        self.free_lists[f as usize][s as usize] = block_to_remove.address;
        */

        /*
        int fl, sl;
        void *big_free_block;
        big_free_block = merge(block); // O(1)
        mapping (sizeof(big_free_block), &fl, &sl);
        insert (big_free_block, fl, sl); // O(1)
        */
    }

    // XXX: This can be done with clever bit manipulation, but we can do it the
    // native way for a V0.
    fn search_suitable_block(&self, size: u32, fl: usize, sl: usize) -> SegList {
        // Find the smallest free block that is larger than the requested size.
        // TODO: include header size into account.

        for f in fl..FIRST_LEVEL_INDEX_SIZE {
            for s in sl..SECOND_LEVEL_INDEX_SIZE {
                if self.free_lists[f][s] != Address::NULL {
                    return SegList(f, s);
                }
            }
        }

        panic!("OOM");
    }
}

#[derive(Debug)]
struct Block {
    address: Address,
    allocated: bool,
    prev_free: Address,
    next_free: Address,
    prev_physical: Address,

    // The size of the block, including the header.
    size: u32,
}

impl Block {
    fn save<M: Memory>(&self, memory: &M) {
        write_struct(
            &BlockHeader {
                allocated: self.allocated,
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
    fn get_next_physical_block<M: Memory>(&self, memory: &M) -> Option<Block> {
        let next_address = self.address + Bytes::from(self.size);

        debug_assert!(next_address <= DATA_OFFSET + Bytes::from(MEMORY_POOL_SIZE));

        if next_address < DATA_OFFSET + Bytes::from(MEMORY_POOL_SIZE) {
            Some(Self::load(next_address, memory))
        } else {
            None
        }
    }

    // Loads the previous physical block in memory.
    // If this is the first physical block in memory, `None` is returned.
    fn get_prev_physical_block<M: Memory>(&self, memory: &M) -> Option<Block> {
        match self.prev_physical {
            Address::NULL => None,
            prev_physical => Some(Self::load(self.prev_physical, memory)),
        }
    }

    // Loads the previous free block if it exists, `None` otherwise.
    fn get_prev_free_block<M: Memory>(&self, memory: &M) -> Option<Block> {
        if self.prev_free != Address::NULL {
            let prev_free = Self::load(self.prev_free, memory);

            // Assert that the previous block is pointing to the current block.
            debug_assert_eq!(prev_free.next_free, self.address);
            // Assert that the previous block is free.
            debug_assert!(!prev_free.allocated);

            Some(prev_free)
        } else {
            None
        }
    }

    // Loads the next free block if it exists, `None` otherwise.
    fn get_next_free_block<M: Memory>(&self, memory: &M) -> Option<Block> {
        if self.next_free != Address::NULL {
            let next_free = Self::load(self.next_free, memory);

            println!("next free block: {:#?}", next_free);
            // Assert that the next block is pointing to the current block.
            debug_assert_eq!(next_free.prev_free, self.address);
            // Assert that the next block is free.
            debug_assert!(!next_free.allocated);

            Some(next_free)
        } else {
            None
        }
    }

    fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: BlockHeader = read_struct(address, memory);
        // TODO: check magic and version?

        Self {
            address,
            allocated: header.allocated,
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
fn mapping(size: u32) -> (u32, u32) {
    let f = u32::BITS - size.leading_zeros() - 1;
    let s = (size ^ (1 << f)) >> (f - SECOND_LEVEL_INDEX_LOG_SIZE as u32);
    (f, s)
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
            assert!((1 << f) + (((1 << f) / SECOND_LEVEL_INDEX_SIZE as u32) * (s + 1) - 1) >= size);
            if s > 0 {
                assert!((1 << f) + ((1 << f) / SECOND_LEVEL_INDEX_SIZE as u32) * s < size);
            }
        });
    }

    #[test]
    fn allocate() {
        let mem = make_memory();
        let mut tlsf = TlsfAllocator::new(mem);
        let block_1 = tlsf.allocate(1232);
        println!("Allocate (1): {:#?}", block_1);

        let block_2 = tlsf.allocate(45);
        println!("Allocate (2): {:#?}", block_2);

        let block_3 = tlsf.allocate(39);
        println!("Allocate (3): {:#?}", block_3);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET
                + Bytes::from(1232u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(45u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(39u64)
                + Bytes::from(Block::header_size())
        );

        println!("== Deallocate (1)");
        tlsf.deallocate(block_1);

        println!("free lists: {:#?}", tlsf.free_lists);

        // block 1 is freed and is in the right list.
        let (f, s) = mapping(1232 + Block::header_size() as u32);
        assert_eq!(tlsf.free_lists[f as usize][s as usize], DATA_OFFSET);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET
                + Bytes::from(1232u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(45u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(39u64)
                + Bytes::from(Block::header_size())
        );

        println!("== Deallocate (2)");
        tlsf.deallocate(block_2);

        // block 2 is freed and is in the right list.
        let (f, s) = mapping(1232 + 45 + Block::header_size() as u32 * 2);
        println!("seg list: {:?}", (f, s));
        assert_eq!(tlsf.free_lists[f as usize][s as usize], DATA_OFFSET);

        println!(
            "BLOCK 2: {:?}",
            Block::load(tlsf.free_lists[f as usize][s as usize], &tlsf.memory),
        );

        println!(
            "BLOCK 2 next: {:?}",
            Block::load(tlsf.free_lists[f as usize][s as usize], &tlsf.memory)
                .get_next_physical_block(&tlsf.memory),
        );

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET
                + Bytes::from(1232u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(45u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(39u64)
                + Bytes::from(Block::header_size())
        );

        println!("== Deallocate (3)");
        tlsf.deallocate(block_3);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET
        );
    }

    #[test]
    fn two_allocate() {
        let mem = make_memory();
        let mut tlsf = TlsfAllocator::new(mem);
        let block_1 = tlsf.allocate(1232);
        println!("Allocate (1): {:#?}", block_1);

        let block_2 = tlsf.allocate(45);
        println!("Allocate (2): {:#?}", block_2);

        let block_3 = tlsf.allocate(39);
        println!("Allocate (3): {:#?}", block_3);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET
                + Bytes::from(1232u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(45u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(39u64)
                + Bytes::from(Block::header_size())
        );

        println!("== Deallocate (3)");
        tlsf.deallocate(block_3);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET
                + Bytes::from(1232u64)
                + Bytes::from(Block::header_size())
                + Bytes::from(45u64)
                + Bytes::from(Block::header_size())
        );

        println!("== Deallocate (2)");
        tlsf.deallocate(block_2);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET + Bytes::from(1232u64) + Bytes::from(Block::header_size())
        );

        println!("== Deallocate (1)");
        tlsf.deallocate(block_1);

        assert_eq!(
            tlsf.free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1],
            DATA_OFFSET
        );
    }
}
