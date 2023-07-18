use super::*;

// There are three types of blocks:
//         remove             allocate
//   Free -------> TempFree ---------> Allocated
//        <-------          <---------
//         insert            deallocate

const FREE_BLOCK_MAGIC: &[u8; 3] = b"FB1"; // Free block v1
const USED_BLOCK_MAGIC: &[u8; 3] = b"UB1"; // Used block v1

// TODO: maybe add a drop flag?
pub struct TempFreeBlock {
    pub address: Address,
    pub prev_physical: Address,
    pub size: u64,
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
}

pub enum Block {
    Free(FreeBlock),
    Used(UsedBlock),
}

impl Block {
    pub fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let mut magic = [0; 3];
        memory.read(address.get(), &mut magic);

        match &magic {
            FREE_BLOCK_MAGIC => Self::Free(FreeBlock::load(address, memory)),
            USED_BLOCK_MAGIC => Self::Used(UsedBlock::load(address, memory)),
            other => panic!("Bag magic {:?}", other),
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

    pub fn size(&self) -> u64 {
        match self {
            Self::Free(b) => b.size,
            Self::Used(b) => b.size,
        }
    }

    pub fn is_free(&self) -> bool {
        match self {
            Self::Free(_) => true,
            Self::Used(_) => false,
        }
    }

    pub fn address(&self) -> Address {
        match self {
            Self::Free(b) => b.address,
            Self::Used(b) => b.address,
        }
    }

    pub fn prev_physical(&self) -> Address {
        match self {
            Self::Free(b) => b.prev_physical,
            Self::Used(b) => b.prev_physical,
        }
    }

    /// Loads the next physical block in memory.
    /// If this is the last physical block in memory, `None` is returned.
    pub(super) fn get_next_physical_block<M: Memory>(
        &self,
        memory: &M,
        data_offset: Address,
    ) -> Option<Block> {
        match self {
            Self::Free(b) => b.get_next_physical_block(memory, data_offset),
            Self::Used(b) => b.get_next_physical_block(memory, data_offset),
        }
    }
}

pub struct UsedBlock {
    pub address: Address,
    prev_physical: Address,
    size: u64,
}

#[derive(Debug, Copy, Clone)]
#[repr(C, packed)]
struct UsedBlockHeader {
    magic: [u8; 3],
    prev_physical: Address,
    size: u64,
}

impl UsedBlock {
    pub fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: UsedBlockHeader = read_struct(address, memory);
        assert_eq!(&header.magic, USED_BLOCK_MAGIC, "Bad magic.");

        Self {
            address,
            prev_physical: header.prev_physical,
            size: header.size,
        }
    }

    pub fn save<M: Memory>(&self, memory: &M) {
        assert!(self.size >= MINIMUM_BLOCK_SIZE);
        write_struct(
            &UsedBlockHeader {
                magic: *USED_BLOCK_MAGIC,
                prev_physical: self.prev_physical,
                size: self.size,
            },
            self.address,
            memory,
        )
    }

    // TODO: maybe introduce a trait or merge the two types?
    /// Loads the next physical block in memory.
    /// If this is the last physical block in memory, `None` is returned.
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

    pub fn deallocate(self) -> TempFreeBlock {
        TempFreeBlock {
            address: self.address,
            prev_physical: self.prev_physical,
            size: self.size,
        }
    }

    pub fn header_size() -> u64 {
        core::mem::size_of::<UsedBlockHeader>() as u64
    }
}

/// An unallocated block of memory.
///
/// # Memory Layout
///
/// ```text
/// -------------------------------------------------- <- Address 0
/// Magic "FC1" (free chunk v1)            ↕ 3 bytes
/// --------------------------------------------------
/// Size                                   ↕ 8 bytes
/// --------------------------------------------------
/// Prev free                              ↕ 8 bytes
/// --------------------------------------------------
/// Next free                              ↕ 8 bytes
/// --------------------------------------------------
/// Previous physical                      ↕ 8 bytes
/// --------------------------------------------------
/// ```
#[derive(Debug, PartialEq, Clone)]
pub struct FreeBlock {
    // TODO: modifications to any of these fields make the block dirty
    pub(super) address: Address,
    pub prev_free: Address,
    pub next_free: Address,
    pub prev_physical: Address,

    // The size of the block, including the header.
    size: u64,

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

#[derive(Debug, Copy, Clone)]
#[repr(C, packed)]
struct FreeBlockHeader {
    magic: [u8; 3],
    prev_free: Address,
    next_free: Address,
    prev_physical: Address,
    size: u64,
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

    pub fn size(&self) -> u64 {
        self.size
    }

    /// Loads a free block from the given address.
    pub(super) fn load<M: Memory>(address: Address, memory: &M) -> Self {
        let header: FreeBlockHeader = read_struct(address, memory);
        assert_eq!(&header.magic, FREE_BLOCK_MAGIC, "Bad magic.");

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
        assert!(self.size >= MINIMUM_BLOCK_SIZE);

        // TODO: same check for previous free and previous physical?
        if self.next_free != Address::NULL {
            assert!(
                self.next_free < self.address
                    || self.next_free >= self.address + Bytes::from(self.size)
            );
        }

        write_struct(
            &FreeBlockHeader {
                magic: *FREE_BLOCK_MAGIC,
                prev_free: self.prev_free,
                next_free: self.next_free,
                prev_physical: self.prev_physical,
                size: self.size,
            },
            self.address,
            memory,
        );

        self.dirty = false;
    }

    /// Loads the next physical block in memory.
    /// If this is the last physical block in memory, `None` is returned.
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

    #[cfg(test)]
    pub fn header_size() -> u64 {
        core::mem::size_of::<FreeBlockHeader>() as u64
    }
}

#[test]
fn test_free_block_header_size() {
    assert_eq!(FreeBlock::header_size(), 35);
    assert_eq!(UsedBlock::header_size(), 19);
}
