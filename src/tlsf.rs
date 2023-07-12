//! TLSF (Two-Level Segregated Free List) Allocator
//! println!("merging next block too!!");
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

#[cfg(test)]
mod tests;

const MAGIC: &[u8; 3] = b"BTA"; // btree allocator
const LAYOUT_VERSION: u8 = 1;

const FIRST_LEVEL_INDEX_SIZE: usize = 32;
const SECOND_LEVEL_INDEX_LOG_SIZE: usize = 5;
const SECOND_LEVEL_INDEX_SIZE: usize = 1 << SECOND_LEVEL_INDEX_LOG_SIZE;

const DATA_OFFSET: Address = Address::new(WASM_PAGE_SIZE);

const MEMORY_POOL_SIZE: u32 = u32::MAX;

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

        let header_addr = Address::NULL; // FIXME
        Self {
            header_addr,
            free_lists,
            memory,
        }
    }

    /// Load an allocator from memory at the given `addr`.
    pub fn load(memory: M, addr: Address) -> Self {
        let header: TlsfHeader = read_struct(addr, &memory);

        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        assert_eq!(header.version, LAYOUT_VERSION, "Unsupported version.");

        assert_eq!(
            addr,
            Address::NULL,
            "we don't yet support arbitrary header addresses"
        );

        Self {
            header_addr: addr,
            free_lists: header.free_lists,
            memory,
        }
    }

    /// Complexity: O(1)
    pub fn allocate(&mut self, size: u32) -> Address {
        self.check_free_lists_invariant();

        // Adjust the size to accommodate the block header.
        let size = size + Block::header_size() as u32;

        let mut block = self.search_suitable_block(size);

        // Remove the block from its free list.
        self.remove(&block);

        if block.size > size {
            // Block is bigger than the requested size. Split it.
            let remaining_size = block.size - size;
            block.size = size;

            // Split the block
            let mut remaining_block = Block {
                address: block.address + size.into(),
                allocated: false,
                prev_free: block.prev_free,
                next_free: Address::NULL, // This is set in the `insert` method.
                size: remaining_size,
                prev_physical: block.address,
            };

            self.insert(&mut remaining_block);
        }

        // Mark the block as allocated.
        block.allocated = true;
        block.save(&self.memory);

        self.check_free_lists_invariant();

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
        //    println!("REMOVE: {:#?}", block);
        // Precondition: `block` is free.
        debug_assert!(!block.allocated);

        match block.get_prev_free_block(&self.memory) {
            None => {
                // `block` is the head of the free list.
                let (f, s) = mapping(block.size);
                println!("updating free list {:?} to {:?}", (f, s), block.next_free);
                debug_assert_eq!(block.address, self.free_lists[f][s]);
                debug_assert_eq!(block.prev_free, Address::NULL);

                //           println!("inserting into seglist {:?} {:?}", (f, s), block.next_free);
                self.free_lists[f][s] = block.next_free;

                if let Some(mut next_block) = block.get_next_free_block(&self.memory) {
                    //              println!("updating prev free from {:?} to null", next_block.prev_free);
                    next_block.prev_free = Address::NULL;
                    next_block.save(&self.memory);
                }
            }
            Some(mut prev_free_block) => {
                //println!("updating prev block: {:?}", prev_free_block);
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
        println!("inserting block: {:#?}", block);
        debug_assert!(!block.allocated);

        let (f, s) = mapping(block.size);
        block.next_free = self.free_lists[f][s];
        println!("SETTING NEXT FREE TO {:?}", block.next_free);

        match block.next_free {
            Address::NULL => {}
            next_free => {
                let mut next_block = Block::load(next_free, &self.memory);
                debug_assert_eq!(next_block.prev_free, Address::NULL);
                debug_assert!(!next_block.allocated);
                next_block.prev_free = block.address;

                println!("saving {:#?}", next_block);
                next_block.save(&self.memory);
            }
        };

        println!("adding block to {:?}", (f, s));
        debug_assert_eq!(block.prev_free, Address::NULL);
        self.free_lists[f][s] = block.address;
        block.save(&self.memory);
    }

    // Merges two free blocks that are physically adjacent to each other.
    fn merge_helper(&mut self, a: Block, b: Block) -> Block {
        println!("MERGE_HELPER");
        println!("removing a: {:#?}", a);
        println!("FL[5]: {:?}", self.free_lists[5][0]);
        println!("FL[6]: {:?}", self.free_lists[6][0]);
        assert!(!a.allocated);
        assert!(!b.allocated);
        assert_eq!(b.prev_physical, a.address);
        assert_eq!(a.address + Bytes::from(a.size), b.address);

        // Remove them from the free lists.
        println!("removing a: {:#?}", a);
        println!("FL[5]: {:?}", self.free_lists[5][0]);
        println!("FL[6]: {:?}", self.free_lists[6][0]);
        self.remove(&a);
        println!("removing b: {:#?}", b);
        println!("FL[5]: {:?}", self.free_lists[5][0]);
        println!("FL[6]: {:?}", self.free_lists[6][0]);
        let b = Block::load(b.address, &self.memory);
        self.remove(&b);

        println!("after removing both");
        println!("FL[5]: {:?}", self.free_lists[5][0]);
        println!("FL[6]: {:?}", self.free_lists[6][0]);

        // Reload them with new pointers.
        let a = Block::load(a.address, &self.memory);
        let b = Block::load(b.address, &self.memory);

        if let Some(mut next_block) = b.get_next_physical_block(&self.memory) {
            assert_eq!(next_block.prev_physical, b.address);
            next_block.prev_physical = a.address;
            next_block.save(&self.memory);
        }

        let mut block = Block {
            address: a.address,
            allocated: false,
            prev_free: Address::NULL,
            next_free: Address::NULL, // to be filled by "insert"
            prev_physical: a.prev_physical,
            size: a.size + b.size,
        };

        self.insert(&mut block);

        println!("DONE MERGE_HELPER");
        println!("FL[5]: {:?}", self.free_lists[5][0]);
        println!("FL[6]: {:?}", self.free_lists[6][0]);
        block
    }

    // Merges a block with its previous and next blocks if they are free.
    // The free lists are updated accordingly.
    fn merge(&mut self, block: Block) -> Block {
        println!("merging block {:?}", block);
        // Precondition: `block` is free.
        debug_assert!(!block.allocated);

        match (
            block.get_prev_physical_block(&self.memory),
            block.get_next_physical_block(&self.memory),
        ) {
            (None, None) => {
                // There are no neighbouring physical blocks. Nothing to do.
                return block;
            }
            (Some(prev_block), None) => {
                if !prev_block.allocated {
                    self.merge_helper(prev_block, block)
                } else {
                    block
                }
            }
            (Some(prev_block), Some(mut next_block)) => {
                println!("prev block: {:?}", prev_block);
                println!("next block: {:?}", next_block);
                if !prev_block.allocated {
                    println!("MERGE CASE 3.1");

                    println!("FL[5]: {:?}", self.free_lists[5][0]);
                    println!("FL[6]: {:?}", self.free_lists[6][0]);

                    println!("prev block: {:?}", prev_block);
                    println!("block: {:?}", block);

                    let mut big_block = self.merge_helper(prev_block, block);

                    println!("FL[5]: {:?}", self.free_lists[5][0]);
                    println!("FL[6]: {:?}", self.free_lists[6][0]);

                    // Reload next block.
                    next_block = Block::load(next_block.address, &self.memory);

                    if !next_block.allocated {
                        println!("merging next block too!!");
                        big_block = self.merge_helper(big_block, next_block);
                        println!("FL[5]: {:?}", self.free_lists[5][0]);
                    }

                    return big_block;
                } else {
                    println!("MERGE CASE 3.2");
                    if !next_block.allocated {
                        return self.merge_helper(block, next_block);
                    }

                    return block;
                }
            }
            (None, Some(next_block)) => {
                println!("MERGE CASE 4");
                if !next_block.allocated {
                    println!(
                        "merging block {:?} with {:?}",
                        block.address, next_block.address
                    );
                    return self.merge_helper(block, next_block);
                }

                return block;
            }
        }
    }

    fn check_free_lists_invariant(&self) {
        let mut total_size = 0;

        let mut free_blocks = std::collections::BTreeMap::new();

        let mut block = Block::load(DATA_OFFSET, &self.memory);
        assert_eq!(block.prev_physical, Address::NULL);
        total_size += block.size;
        if !block.allocated {
            free_blocks.insert(block.address, block.clone());
        }

        while let Some(next_block) = block.get_next_physical_block(&self.memory) {
            block = next_block;
            total_size += block.size;
            if !block.allocated {
                free_blocks.insert(block.address, block.clone());
            }
        }

        // The sum of all the block sizes = MEMORY POOL.
        assert_eq!(total_size, MEMORY_POOL_SIZE);

        // Links between all free blocks are correct.
        /*for free_block in free_blocks.values() {
            if free_block.prev_free != Address::NULL {
                println!("attempting to load prev block {:?}", free_block.prev_free);
                assert_eq!(
                    free_blocks.get(&free_block.prev_free).unwrap().next_free,
                    free_block.address
                );
            }
        }*/

        /*let mut free_blocks_2 = std::collections::BTreeMap::new();
        for f in 0..FIRST_LEVEL_INDEX_SIZE {
            for s in 0..SECOND_LEVEL_INDEX_SIZE {
                if self.free_lists[f][s] != Address::NULL {
                    let head = Block::load(self.free_lists[f][s], &self.memory);
                    println!("seg list {:?}", (f, s));
                    println!("head block: {:#?}", head);
                    assert_eq!(head.prev_free, Address::NULL);

                    // No duplicates.
                    assert_eq!(free_blocks_2.insert(self.free_lists[f][s], ()), None);
                }
            }
        }*/
    }

    /// Deallocates a previously allocated block.
    ///
    /// PRECONDITION:
    ///   * `address` points to an allocated block.
    ///
    /// POSTCONDITION:
    ///   * The block with `address` is freed, and merged with its neighbouring free blocks.
    ///   TODO: explore how to make this more precise and add programmatic checks.
    pub fn deallocate(&mut self, address: Address) {
        self.check_free_lists_invariant();

        let address = address - Bytes::from(Block::header_size());
        let mut block = Block::load(address, &self.memory);

        println!("=============== Deallocating block {:#?}", block);

        debug_assert!(
            block.allocated,
            "cannot deallocate an already deallocated block."
        );

        // Free the block.
        block.allocated = false;
        self.insert(&mut block);

        self.merge(block);

        self.check_free_lists_invariant();

        // TODO: should insertion be another explicit step?
    }

    pub fn save(&self) {
        // XXX: don't assume the header is stored at address 0.
        write_struct(
            &TlsfHeader {
                magic: *MAGIC,
                version: LAYOUT_VERSION,
                free_lists: self.free_lists.clone(),
            },
            Address::NULL,
            &self.memory,
        );
    }

    // Returns the smallest block that accommodates the size.
    //
    // XXX: This can be done with clever bit manipulation, but we can do it the
    // naive way for a V0.
    fn search_suitable_block(&self, size: u32) -> Block {
        // Identify the free list to take blocks from.
        let (fl, sl) = mapping(size);
        let (fl, sl) = (fl as usize, sl as usize);

        // Find the smallest free block that is larger than the requested size.
        for f in fl..FIRST_LEVEL_INDEX_SIZE {
            for s in sl..SECOND_LEVEL_INDEX_SIZE {
                if self.free_lists[f][s] != Address::NULL {
                    let block = Block::load(self.free_lists[f][s], &self.memory);

                    // The block must be:
                    // (1) The head of its free list.
                    debug_assert_eq!(block.prev_free, Address::NULL);
                    // (2) Free
                    debug_assert!(!block.allocated);
                    // (3) Big enough
                    debug_assert!(block.size >= size);

                    return block;
                }
            }
        }

        panic!("OOM");
    }
}

#[derive(Debug, PartialEq, Clone)]
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
        //    println!("about to save block: {:#?}", self);
        if self.next_free != Address::NULL {
            assert!(
                self.next_free < self.address
                    || self.next_free >= self.address + Bytes::from(self.size)
            );
        }

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
            let block = Self::load(next_address, memory);
            debug_assert_eq!(block.prev_physical, self.address);
            Some(block)
        } else {
            None
        }
    }

    // Loads the previous physical block in memory.
    // If this is the first physical block in memory, `None` is returned.
    fn get_prev_physical_block<M: Memory>(&self, memory: &M) -> Option<Block> {
        match self.prev_physical {
            Address::NULL => None,
            prev_physical => Some(Self::load(prev_physical, memory)),
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
            //debug_assert_eq!(next_free.prev_free, self.address);
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
