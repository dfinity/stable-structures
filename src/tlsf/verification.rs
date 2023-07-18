use super::*;

impl<M: Memory> TlsfAllocator<M> {
    pub fn check_invariants(&self) -> bool {
        let mut block = Block::load(self.data_offset(), &self.memory);
        let mut total_size = block.size();
        let mut num_free_blocks = if block.is_free() { 1 } else { 0 };

        while let Some(next_block) = block.get_next_physical_block(&self.memory, self.data_offset())
        {
            // Invariant: physical blocks are properly linked to each other.
            assert_eq!(
                block.address() + Bytes::from(block.size()),
                next_block.address()
            );
            assert_eq!(next_block.prev_physical(), block.address(),);

            if next_block.is_free() {
                num_free_blocks += 1;
            }

            block = next_block;
            total_size += block.size();
        }

        // Invariant: The sum of the blocks' sizes == MEMORY_POOL_SIZE
        assert_eq!(total_size, MEMORY_POOL_SIZE);

        let mut num_free_blocks_in_free_lists = 0;
        for f in 0..FIRST_LEVEL_INDEX_SIZE {
            for s in 0..SECOND_LEVEL_INDEX_SIZE {
                if self.free_lists[f][s] != Address::NULL {
                    // Non-empty free list. Iterate through it and count number of blocks.
                    let mut block = FreeBlock::load(self.free_lists[f][s], &self.memory);
                    num_free_blocks_in_free_lists += 1;
                    assert_eq!(block.prev_free, Address::NULL);

                    while let Some(next_block) = block.get_next_free_block(&self.memory) {
                        num_free_blocks_in_free_lists += 1;

                        // Invariant: free blocks are properly linked to each other.
                        assert_eq!(next_block.prev_free, block.address);
                        assert_eq!(block.next_free, next_block.address);

                        block = next_block;

                        // TODO: invariant on block sizes.
                    }
                }
            }
        }

        // Invariant: The number of free blocks found when traversing blocks in physical order
        // is the same as when the free blocks are traversed via the free lists.
        assert_eq!(num_free_blocks, num_free_blocks_in_free_lists);

        true
    }

    pub fn block_is_allocated(&self, address: Address) -> bool {
        let address = address - Bytes::from(UsedBlock::header_size());
        !Block::load(address, &self.memory).is_free()
    }
}
