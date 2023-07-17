use super::*;

impl<M: Memory> TlsfAllocator<M> {
    /// Invariant: The size of all blocks == MEMORY_POOL_SIZE
    pub(super) fn memory_size_invariant(&self) {
        let mut block = Block::load(self.data_offset(), &self.memory);
        let mut total_size = block.size();

        while let Some(next_block) = block.get_next_physical_block(&self.memory, self.data_offset())
        {
            // Verify that the physical blocks properly link to each other.
            assert_eq!(
                block.address() + Bytes::from(block.size()),
                next_block.address()
            );

            block = next_block;
            total_size += block.size();
        }

        assert_eq!(total_size, MEMORY_POOL_SIZE);
    }

    pub(super) fn physical_blocks_are_properly_linked(&self) {
        let mut block = Block::load(self.data_offset(), &self.memory);
        let mut total_size = block.size();

        while let Some(next_block) = block.get_next_physical_block(&self.memory, self.data_offset())
        {
            block = next_block;
            total_size += block.size();
        }

        assert_eq!(total_size, MEMORY_POOL_SIZE);
    }

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
