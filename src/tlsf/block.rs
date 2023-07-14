use super::*;

// There are three types of blocks:
//         remove             allocate
//   Free -------> TempFree ---------> Allocated
//        <-------          <---------
//         insert            deallocate


// TODO: maybe add a drop flag?
pub struct TempFreeBlock {
    pub address: Address,
    pub prev_physical: Address,
    pub size: u32,
}

impl TempFreeBlock {
    pub fn allocate(self) -> UsedBlock {
        UsedBlock {
            address: self.address,
            prev_physical: self.prev_physical,
            size: self.size,
        }
    }

    pub fn into_free_block(self, next_free: Address) -> FreeBlock {
        FreeBlock {
            address: self.address,
            prev_free: Address::NULL,
            next_free,
            prev_physical: self.prev_physical,
            size: self.size,
            dirty: true,
        }
    }

    // TODO: maybe a split method?
}

pub enum Block {
    Free(FreeBlock),
    Used(UsedBlock),
}

impl Block {
    pub fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: BlockHeader = read_struct(address, memory);

        // TODO: avoid reading the header twice.
        match header.allocated {
            false => Self::Free(FreeBlock::load(address, memory)),
            true => Self::Used(UsedBlock::load(address, memory)),
        }
    }

    // TODO: consider removing this.
    pub fn set_prev_physical(&mut self, prev_physical: Address) {
        match self {
            Self::Free(b) => b.prev_physical = prev_physical,
            Self::Used(b) => b.prev_physical = prev_physical,
        }
    }

    pub fn save<M: Memory>(&mut self, memory: &M) {
        match self {
            Self::Free(b) => b.save(memory),
            Self::Used(b) => b.save(memory),
        }
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

pub struct UsedBlock {
    pub address: Address,
    prev_physical: Address,
    size: u32,
}

impl UsedBlock {
    pub fn load<M: Memory>(address: Address, memory: &M) -> Self {
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

    pub fn save<M: Memory>(&self, memory: &M) {
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

    pub fn deallocate(self) -> TempFreeBlock {
        TempFreeBlock {
            address: self.address,
            prev_physical: self.prev_physical,
            size: self.size,
        }
    }

    // TODO: used block headers are smaller.
    pub fn header_size() -> u64 {
        core::mem::size_of::<BlockHeader>() as u64
    }
}

/// An unallocated block of memory.
#[derive(Debug, PartialEq, Clone)]
pub struct FreeBlock {
    // TODO: modifications to any of these fields make the block dirty
    pub(super) address: Address,
    pub prev_free: Address,
    pub next_free: Address,
    pub prev_physical: Address,

    // The size of the block, including the header.
    size: u32,

    dirty: bool,
}

#[cfg(test)]
impl Drop for FreeBlock {
    fn drop(&mut self) {
        if self.dirty {
            panic!("cannot drop an unsaved free block");
        }
    }
}

impl FreeBlock {
    pub fn genesis(address: Address) -> Self {
        FreeBlock {
            address,
            size: MEMORY_POOL_SIZE,
            prev_free: Address::NULL,
            next_free: Address::NULL,
            prev_physical: Address::NULL,
            dirty: false, // FIXME: what should this be?
        }
    }

    pub fn size(&self) -> u32 {
        self.size
    }

    /// Loads a free block from the given address.
    pub(super) fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: BlockHeader = read_struct(address, memory);
        // TODO: check magic and version?
        assert!(!header.allocated);

        Self {
            address,
            prev_free: header.prev_free,
            next_free: header.next_free,
            size: header.size,
            prev_physical: header.prev_physical,
            dirty: false,
        }
    }

    pub fn save<M: Memory>(&mut self, memory: &M) {
        // TODO: save check for previous free and previous physical?
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
        );

        self.dirty = false;
    }

    // Loads the next physical block in memory.
    // If this is the last physical block in memory, `None` is returned.
    pub(super) fn get_next_physical_block<M: Memory>(
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
    pub(super) fn get_prev_physical_block<M: Memory>(&self, memory: &M) -> Option<Block> {
        match self.prev_physical {
            // TODO: in prev physical is null, maybe assert that block's address is the data
            // offset?
            Address::NULL => None,
            prev_physical => Some(Block::load(prev_physical, memory)),
        }
    }

    // Loads the previous free block if it exists, `None` otherwise.
    pub fn get_prev_free_block<M: Memory>(&self, memory: &M) -> Option<FreeBlock> {
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
    pub fn get_next_free_block<M: Memory>(&self, memory: &M) -> Option<FreeBlock> {
        if self.next_free != Address::NULL {
            let next_free = Self::load(self.next_free, memory);

            // Assert that the next block is pointing to the current block.
            assert_eq!(next_free.prev_free, self.address);

            Some(next_free)
        } else {
            None
        }
    }

    pub fn header_size() -> u64 {
        core::mem::size_of::<BlockHeader>() as u64
    }
}
