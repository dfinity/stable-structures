//! TLSF (Two-Level Segregated Free List) Allocator
//!
//! This is a dynamic memory allocator that's constant time and provides reasonable fragmentation
//! bounds.
//!
//! Benefits:
//! * O(1) allocation and deallocation
//! * Same strategy for all block sizes

use crate::{types::Address, write_struct, Memory, WASM_PAGE_SIZE};

// As defined in the paper.
const MINIMUM_BLOCK_SIZE: u32 = 16;

const FIRST_LEVEL_INDEX_SIZE: usize = 32;
const SECOND_LEVEL_INDEX_LOG_SIZE: usize = 5;
const SECOND_LEVEL_INDEX_SIZE: usize = 1 << SECOND_LEVEL_INDEX_LOG_SIZE;

const DATA_OFFSET: Address = Address::new(WASM_PAGE_SIZE);

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
        let block = BlockHeader {
            size: u32::MAX,
            next: Address::NULL,
        };

        block.save(DATA_OFFSET, &memory);

        free_lists[FIRST_LEVEL_INDEX_SIZE - 1][SECOND_LEVEL_INDEX_SIZE] = DATA_OFFSET;

        Self { free_lists, memory }
    }

    fn insert_block() {
        todo!();
    }

    // TODO: load, init

    pub fn allocate(&mut self, size: u32) -> Address {
        let (fl, sl) = mapping(size);

        // XXX: This can be done with clever bit manipulation, but we can do it the
        // native way for a V0.
        //found_block=search_suitable_block(size,fl,sl);// O(1)

        /*
        remove (found_block); // O(1)
        if (sizeof(found_block)>size) {
        remaining_block = split (found_block, size);
        mapping (sizeof(remaining_block),&fl2,&sl2);
        insert (remaining_block, fl2, sl2); // O(1)
        }
        remove (found_block); // O(1)
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

    fn search_suitable_block(size: u32, fl: usize, sl: usize) {
        todo!();
    }
}

#[derive(Debug, Copy, Clone)]
#[repr(C, packed)]
struct BlockHeader {
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
    /*println!("{}", SECOND_LEVEL_INDEX_SIZE);
    let fl = size.leading_zeros() as u32 + 1;
    println!("fl << {}", 1 << fl);
    println!("fl << {}", 1 << 31);
    //let sl = (size ^ (1 << fl)) >> (fl - SECOND_LEVEL_INDEX_LOG_SIZE as u32);
    let sl = (size ^ (1 << fl)) * ((1 << SECOND_LEVEL_INDEX_LOG_SIZE) / (1 << fl));
    println!("step 1: {}", (size ^ (1 << fl)));
    (fl, sl)*/

    // XXX: REVISE this.
    let mut fl = u32::BITS - 1 - size.leading_zeros();

    // The shift amount can be negative, and rotation lets us handle both
    // cases without branching.
    let mut sl = size.rotate_right((fl).wrapping_sub(SECOND_LEVEL_INDEX_LOG_SIZE as u32));

    // The most significant one of `size` should be now at `sl[SLI]`
    //debug_assert!(((sl >> Self::SLI) & 1) == 1);

    // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
    // be rounded up
    sl = (sl & (SECOND_LEVEL_INDEX_SIZE as u32 - 1))
        + (sl >= (1 << (SECOND_LEVEL_INDEX_LOG_SIZE as u32 + 1))) as u32;

    // if sl[SLI] { fl += 1; sl = 0; }
    fl += (sl >> SECOND_LEVEL_INDEX_LOG_SIZE) as u32;

    // `fl` must be in a valid range
    if fl >= FIRST_LEVEL_INDEX_SIZE as u32 {
        panic!("what to do here?");
    }

    (fl as u32, sl & (SECOND_LEVEL_INDEX_SIZE as u32 - 1))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn mapping_test() {
        //        println!("mapping: {:?}", mapping(123421));
        assert_eq!(mapping(123421), (16, 29));
    }
}
