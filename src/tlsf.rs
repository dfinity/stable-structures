//! TLSF (Two-Level Segregated Free List) Allocator
//!
//! This is a dynamic memory allocator that's constant time and provides reasonable fragmentation
//! bounds.
//!
//! Benefits:
//! * O(1) allocation and deallocation
//! * Same strategy for all block sizes

use crate::{read_struct, types::Address, write_struct, Memory, WASM_PAGE_SIZE};

// As defined in the paper.
const MINIMUM_BLOCK_SIZE: u32 = 16;

const FIRST_LEVEL_INDEX_SIZE: usize = 32;
const SECOND_LEVEL_INDEX_LOG_SIZE: usize = 5;
const SECOND_LEVEL_INDEX_SIZE: usize = 1 << SECOND_LEVEL_INDEX_LOG_SIZE;

const DATA_OFFSET: Address = Address::new(WASM_PAGE_SIZE);

struct SegList(usize, usize);

//const GRANULARITY_LOG2: u32 = GRANULARITY.trailing_zeros();

fn find_lowest_set_bit(mut word: u32) -> u32 {
    word.leading_zeros()
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
            size: u32::MAX,
            next: Address::NULL,
        };

        block.save(&memory);

        free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE - 1] = DATA_OFFSET;

        Self { free_lists, memory }
    }

    // TODO: load, init

    pub fn allocate(&mut self, size: u32) -> Address {
        let (fl, sl) = mapping(size);

        let block_seg_list = self.search_suitable_block(size, fl as usize, sl as usize);

        let mut block = Block::load(
            self.free_lists[block_seg_list.0][block_seg_list.1],
            &self.memory,
        );
        println!("Got block {:?}", block);

        // Remove the block
        self.free_lists[block_seg_list.0][block_seg_list.1] = block.next;
        block.allocated = true;

        if block.size > size {
            let remaining_size = block.size - size - Block::header_size() as u32;
            println!("remaining size: {}", remaining_size);
            let (fl, sl) = mapping(remaining_size);
            println!("remaining seg list {:?}", (fl, sl));
        }

        //found_block=search_suitable_block(size,fl,sl);// O(1)

        /*
        remove (found_block); // O(1)
        if (sizeof(found_block)>size) {
        remaining_block = split (found_block, size);
        mapping (sizeof(remaining_block),&fl2,&sl2);
        insert (remaining_block, fl2, sl2); // O(1)
        }
        return found_block;*/
        todo!();
    }

    pub fn deallocate(&mut self, address: Address) {
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
    next: Address,
    size: u32,
}

impl Block {
    fn save<M: Memory>(&self, memory: &M) {
        write_struct(
            &BlockHeader {
                allocated: self.allocated,
                next: self.next,
                size: self.size,
            },
            self.address,
            memory,
        )
    }

    fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: BlockHeader = read_struct(address, memory);
        // TODO: check magic and version?

        Self {
            address,
            allocated: header.allocated,
            next: header.next,
            size: header.size,
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
    next: Address,
}

impl BlockHeader {
    fn save<M: Memory>(&self, address: Address, memory: &M) {
        write_struct(self, address, memory);
    }
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
        //        println!("mapping: {:?}", mapping(123421));
        assert_eq!(mapping(32), (5, 0));
        assert_eq!(mapping(63), (5, 31));

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
        tlsf.allocate(1232);
    }
}
