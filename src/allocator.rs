type MemoryAddress = u32;

#[derive(Debug, PartialEq, Eq)]
pub enum AllocError {
    GrowFailed { current: u32, delta: u32 },
    AddressSpaceOverflow,
}

/// An interface for memory allocators.
///
/// The API is inspired by https://doc.rust-lang.org/std/alloc/trait.Allocator.html.
pub trait Allocator {
    /// Allocates a piece of memory with the given size and returns its address.
    // TODO: support memory alignment?
    fn allocate(&self, size: u32) -> Result<MemoryAddress, AllocError>;

    fn deallocate(&self, addr: MemoryAddress, size: u32);

    /// Allocates a piece of memory with the given size and returns its address.
    /// The memory is initialized with zeros.
    fn allocate_zeroed(&self, size: u32) -> Result<MemoryAddress, AllocError>;
}

pub mod mock_allocator {
    use super::*;
    use crate::{Memory, WASM_PAGE_SIZE};

    const LAYOUT_VERSION: u8 = 0;

    #[derive(Debug, PartialEq, Eq)]
    pub enum LoadError {
        MemoryEmpty,
        BadMagic([u8; 3]),
        UnsupportedVersion(u8),
    }

    /// A very simple proof-of-concept allocator.
    ///
    /// This allocator never frees memory and should never be used in production.
    pub struct MockAllocator<M: Memory> {
        memory: M,
    }

    #[repr(packed)]
    struct MockAllocatorHeader {
        magic: [u8; 3],
        version: u8,
        free_offset: u32,
    }

    impl<M: Memory> MockAllocator<M> {
        /// Initializes the allocator given a memory.
        ///
        /// The allocator checks if it was ever initialized in this memory before
        /// and, if yes, loads its configuration from memory.
        pub fn new(memory: M) -> Result<Self, AllocError> {
            if memory.size() < 1 && memory.grow(1) == -1 {
                return Err(AllocError::GrowFailed {
                    current: 0,
                    delta: 1,
                });
            }

            // NOTE: the first 8 bytes of the memory is reserved for the root data,
            // so we assume that allocator's header is stored in address 8.
            let mut magic = vec![0; 3];
            memory.read(8, &mut magic);

            if magic == *b"DAL" {
                // If magic is there, meaning that the allocator was initialized in
                // this memory previously. Load instead.
                // TODO: properly handle error here.
                return Ok(Self::load(memory).unwrap());
            }

            let header_len = core::mem::size_of::<MockAllocatorHeader>() as u32;

            let header = MockAllocatorHeader {
                magic: *b"DAL",
                version: LAYOUT_VERSION,
                free_offset: header_len + 8, // beginning of free space.
            };

            let header_slice = unsafe {
                core::slice::from_raw_parts(
                    &header as *const _ as *const u8,
                    core::mem::size_of::<MockAllocatorHeader>(),
                )
            };

            // NOTE: the first 8 bytes of the memory is reserved for the root data,
            // so we store allocator's header in address 8.
            memory.write(8, header_slice);

            Ok(Self { memory })
        }

        /// Load the pre-initialized allocator from memory.
        pub fn load(memory: M) -> Result<Self, LoadError> {
            let mut header: MockAllocatorHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<MockAllocatorHeader>(),
                )
            };
            if memory.size() == 0 {
                return Err(LoadError::MemoryEmpty);
            }
            memory.read(8, header_slice);

            if &header.magic != b"DAL" {
                return Err(LoadError::BadMagic(header.magic));
            }

            if header.version != LAYOUT_VERSION {
                return Err(LoadError::UnsupportedVersion(header.version));
            }

            Ok(Self { memory })
        }

        // Gets the pointer to the free area of memory. The allocator that all the memory
        // after this address is free.
        fn get_free_offset(&self) -> u32 {
            let mut header: MockAllocatorHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<MockAllocatorHeader>(),
                )
            };
            self.memory.read(8, header_slice);
            header.free_offset
        }

        // Sets the pointer to the free area of memory.
        fn set_free_offset(&self, new_free_offset: u32) {
            let mut header: MockAllocatorHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<MockAllocatorHeader>(),
                )
            };
            // NOTE: the first 8 bytes of the memory is reserved for the root data,
            // so we assume that allocator's header is stored in address 8.
            self.memory.read(8, header_slice);
            header.free_offset = new_free_offset;
            self.memory.write(8, header_slice);
        }
    }

    impl<M: Memory> Allocator for MockAllocator<M> {
        /// Allocate an arbitrarily sized area of memory. The algorithm here is very simple.
        fn allocate(&self, size: u32) -> Result<u32, AllocError> {
            // Pointer to the free area in memory. We assume that all memory after
            // this address is free.
            let free_offset = self.get_free_offset();

            let memory_size_in_bytes = self
                .memory
                .size()
                .checked_mul(WASM_PAGE_SIZE)
                .ok_or(AllocError::AddressSpaceOverflow)?;

            let bytes_needed = free_offset
                .checked_add(size)
                .ok_or(AllocError::AddressSpaceOverflow)?;

            // Grow memory if necessary.
            if memory_size_in_bytes < bytes_needed {
                let extra_pages = (((bytes_needed - memory_size_in_bytes) as f32)
                    / WASM_PAGE_SIZE as f32)
                    .ceil() as u32;
                if self.memory.grow(extra_pages) == -1 {
                    return Err(AllocError::GrowFailed {
                        current: 0,
                        delta: 1,
                    });
                }
            }

            self.set_free_offset(free_offset + size);

            Ok(free_offset)
        }

        fn allocate_zeroed(&self, size: u32) -> Result<u32, AllocError> {
            // NOTE: this is a very inefficient way to zero the memory.
            let ptr = self.allocate(size)?;
            let zeros = vec![0; size as usize];
            self.memory.write(ptr, &zeros);
            Ok(ptr)
        }

        fn deallocate(&self, _addr: u32, _size: u32) {
            // The mock allocator never frees memory. Bad bad bad...
        }
    }
}
