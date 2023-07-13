use super::*;

impl<M: Memory> TlsfAllocator<M> {
    pub(super) fn check_free_lists_invariant(&self) -> bool {
        let mut total_size = 0;

        let mut free_blocks = std::collections::BTreeMap::new();

        let mut block = Block::load(self.data_offset(), &self.memory);
        assert_eq!(block.prev_physical, Address::NULL);
        total_size += block.size;
        if !block.allocated {
            free_blocks.insert(block.address, block.clone());
        }

        while let Some(next_block) = block.get_next_physical_block(&self.memory, self.data_offset())
        {
            block = next_block;
            total_size += block.size;
            if !block.allocated {
                free_blocks.insert(block.address, block.clone());
            }
        }

        // The sum of all the block sizes = MEMORY POOL.
        if total_size != MEMORY_POOL_SIZE {
            return false;
        }

        true

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
}
