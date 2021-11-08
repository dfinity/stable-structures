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
    /// Allocates a piece of memory with the given size, and return its pointer.
    // TODO: add layout?
    fn allocate(&self, size: u32) -> Result<MemoryAddress, AllocError>;

    fn deallocate(&self, addr: MemoryAddress, size: u32);

    fn allocate_zeroed(&self, size: u32) -> Result<MemoryAddress, AllocError>;
}

//#[cfg(test)]
pub mod dumb_allocator {
    use super::*;
    use crate::{Memory, WASM_PAGE_SIZE};

    const LAYOUT_VERSION: u8 = 0;

    #[derive(Debug, PartialEq, Eq)]
    pub enum LoadError {
        MemoryEmpty,
        BadMagic([u8; 3]),
        UnsupportedVersion(u8),
    }

    pub struct DumbAllocator<M: Memory> {
        memory: M,
    }

    #[repr(packed)]
    struct DumbAllocatorHeader {
        magic: [u8; 3],
        version: u8,
        free_offset: u32,
        root_address: u32,
        root_size: u32,
    }

    impl<M: Memory> DumbAllocator<M> {
        pub fn new(memory: M) -> Result<(Self, Option<Vec<u8>>), AllocError> {
            if memory.size() < 1 && memory.grow(1) == -1 {
                return Err(AllocError::GrowFailed {
                    current: 0,
                    delta: 1,
                });
            }

            // If magic is there, load instead.
            let mut x = vec![0; 3];
            memory.read(0, &mut x);

            if x == *b"DAL" {
                let loaded = Self::load(memory).unwrap();
                return Ok((loaded.0, loaded.1));
            }

            let header_len = core::mem::size_of::<DumbAllocatorHeader>() as u32;

            let header = DumbAllocatorHeader {
                magic: *b"DAL",
                version: LAYOUT_VERSION,
                free_offset: header_len, // beginning of free space.
                root_address: 0,
                root_size: 0,
            };

            let header_slice = unsafe {
                core::slice::from_raw_parts(
                    &header as *const _ as *const u8,
                    core::mem::size_of::<DumbAllocatorHeader>(),
                )
            };

            memory.write(0, header_slice);

            Ok((Self { memory }, None))
        }

        pub fn pre_upgrade(&self, index: &[u8]) {
            // TODO: deallocate previous data.
            let root_address = self.allocate(index.len() as u32).unwrap();

            self.memory.write(root_address, index);

            let mut header: DumbAllocatorHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<DumbAllocatorHeader>(),
                )
            };
            self.memory.read(0, header_slice);

            header.root_address = root_address;
            header.root_size = index.len() as u32;

            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<DumbAllocatorHeader>(),
                )
            };
            self.memory.write(0, header_slice);
        }

        pub fn load(memory: M) -> Result<(Self, Option<Vec<u8>>), LoadError> {
            let mut header: DumbAllocatorHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<DumbAllocatorHeader>(),
                )
            };
            if memory.size() == 0 {
                return Err(LoadError::MemoryEmpty);
            }
            memory.read(0, header_slice);

            if &header.magic != b"DAL" {
                return Err(LoadError::BadMagic(header.magic));
            }

            if header.version != LAYOUT_VERSION {
                return Err(LoadError::UnsupportedVersion(header.version));
            }

            let root_data = if header.root_size == 0 {
                None
            } else {
                let mut d = vec![0; header.root_size as usize];
                memory.read(header.root_address, &mut d);
                Some(d)
            };

            Ok((Self { memory }, root_data))
        }

        fn get_free_offset(&self) -> u32 {
            let mut header: DumbAllocatorHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<DumbAllocatorHeader>(),
                )
            };
            self.memory.read(0, header_slice);
            header.free_offset
        }

        fn set_free_offset(&self, new_free_offset: u32) {
            let mut header: DumbAllocatorHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<DumbAllocatorHeader>(),
                )
            };
            self.memory.read(0, header_slice);
            header.free_offset = new_free_offset;
            self.memory.write(0, header_slice);
        }
    }

    impl<M: Memory> Allocator for DumbAllocator<M> {
        fn allocate(&self, size: u32) -> Result<u32, AllocError> {
            let free_offset = self.get_free_offset();

            let memory_size_in_bytes = self
                .memory
                .size()
                .checked_mul(WASM_PAGE_SIZE)
                .ok_or(AllocError::AddressSpaceOverflow)?;

            let bytes_needed = free_offset
                .checked_add(size)
                .ok_or(AllocError::AddressSpaceOverflow)?;

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
            // TODO: grow memory if needed.

            let old_free_offset = self.get_free_offset();

            self.set_free_offset(old_free_offset + size);

            Ok(old_free_offset)
        }

        fn allocate_zeroed(&self, size: u32) -> Result<u32, AllocError> {
            let ptr = self.allocate(size)?;
            let zeros = vec![0; size as usize];
            self.memory.write(ptr, &zeros);
            Ok(ptr)
        }

        fn deallocate(&self, _addr: u32, _size: u32) {
            // A dumb allocator never frees memory.
        }
    }
}
