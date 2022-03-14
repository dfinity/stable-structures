use crate::btree::{write, LoadError, WriteError};
use crate::{Memory64, WASM_PAGE_SIZE};

const ALLOCATOR_LAYOUT_VERSION: u8 = 1;
const CHUNK_LAYOUT_VERSION: u8 = 1;

type Ptr = u64;
const NULL: Ptr = 0;

/// A free list constant-size chunk allocator.
///
/// NOTE: we're not really tracking free chunks.
pub struct Allocator<M: Memory64> {
    // The address in memory where the allocator header is stored.
    addr: Ptr,

    // The size of the chunk to allocate in bytes.
    chunk_size: u32,

    // The number of chunks currently allocated.
    num_allocations: u64,

    memory: M,
    head: Ptr,
}

#[repr(packed)]
struct AllocatorHeader {
    magic: [u8; 3],
    version: u8,
    chunk_size: u32,
    num_allocations: u64,

    // Pointer to the first empty chunk.
    head: Ptr,
}

impl<M: Memory64> Allocator<M> {
    /// Initialize an allocator and store it in address `addr`.
    ///
    /// The allocator assumes that all memory from `addr` onwards is free.
    pub fn new(memory: M, addr: Ptr, chunk_size: u32) -> Result<Self, WriteError> {
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        let head = addr + header_len;

        // Create the initial memory chunk and save it directly after the allocator's header.
        let chunk = Chunk::default();
        chunk.save(head, &memory)?;

        let allocator = Self {
            addr,
            chunk_size,
            num_allocations: 0,
            head,
            memory,
        };

        allocator.save()?;

        Ok(allocator)
    }

    /// Load an allocator from memory at address `addr`.
    pub fn load(memory: M, addr: Ptr) -> Result<Self, LoadError> {
        let mut header: AllocatorHeader = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<AllocatorHeader>(),
            )
        };
        if memory.size() == 0 {
            return Err(LoadError::MemoryEmpty);
        }
        memory.read(addr, header_slice);
        if &header.magic != b"BTA" {
            println!("magic found: {:?}", header.magic);
            println!("magic expected: {:?}", b"BTA");
            return Err(LoadError::BadMagic(header.magic));
        }
        if header.version != ALLOCATOR_LAYOUT_VERSION {
            return Err(LoadError::UnsupportedVersion(header.version));
        }
        Ok(Self {
            addr,
            chunk_size: header.chunk_size,
            num_allocations: header.num_allocations,
            head: header.head,
            memory,
        })
    }

    /// Allocates a new chunk from memory with size `chunk_size`.
    pub fn allocate(&mut self) -> Result<Ptr, WriteError> {
        let head_chunk = Chunk::load(self.head, &self.memory).expect("Loading chunk cannot fail");

        let new_chunk_addr = self.head;

        if head_chunk.next != NULL {
            // The next chunk becomes the new head of the list.
            let new_head =
                Chunk::load(head_chunk.next, &self.memory).expect("Loading chunk cannot fail");
            new_head.save(head_chunk.next, &self.memory)?;
            self.head = head_chunk.next;
        } else {
            // There is no next chunk. Shift everything by chunk size.
            self.head += self.chunk_size as u64;

            // Write new chunk to that location.
            Chunk::default().save(self.head, &self.memory)?;
        }

        self.num_allocations += 1;
        self.save()?;
        Ok(new_chunk_addr)
    }

    /// We assume the caller is passing in the correct pointer.
    /// and the caller never deallocates the same address more than once.
    pub fn deallocate(&mut self, address: Ptr) {
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        debug_assert!(address >= self.addr + header_len);
        debug_assert_eq!(
            (address - header_len - self.addr) % self.chunk_size as u64,
            0
        );

        let chunk = Chunk::new(self.head);
        chunk
            .save(address, &self.memory)
            .expect("Save to a previously allocated chunk cannot fail");

        self.head = address;

        self.num_allocations -= 1;
        self.save()
            .expect("Saving the allocator's state cannot fail");
    }

    /// Returns the number of chunks currently allocated.
    pub fn num_allocations(&self) -> u64 {
        self.num_allocations
    }

    pub fn save(&self) -> Result<(), WriteError> {
        let header = AllocatorHeader {
            magic: *b"BTA", // btree allocator
            version: ALLOCATOR_LAYOUT_VERSION,
            num_allocations: self.num_allocations,
            chunk_size: self.chunk_size,
            head: self.head,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<AllocatorHeader>(),
            )
        };

        write(&self.memory, self.addr, header_slice)
    }
}

#[repr(packed)]
struct Chunk {
    magic: [u8; 3],
    version: u8,
    next: Ptr,
}

impl Default for Chunk {
    fn default() -> Self {
        Chunk {
            magic: *b"CHK",
            version: CHUNK_LAYOUT_VERSION,
            next: NULL,
        }
    }
}

impl Chunk {
    fn new(next: Ptr) -> Self {
        Chunk {
            magic: *b"CHK",
            version: CHUNK_LAYOUT_VERSION,
            next,
        }
    }

    fn save(&self, address: Ptr, memory: &impl Memory64) -> Result<(), WriteError> {
        let chunk_slice = unsafe {
            core::slice::from_raw_parts(self as *const _ as *const u8, core::mem::size_of::<Self>())
        };

        write(memory, address, chunk_slice)
    }

    fn load(address: Ptr, memory: &impl Memory64) -> Result<Self, LoadError> {
        let mut header: Chunk = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<Chunk>(),
            )
        };

        memory.read(address, header_slice);

        if &header.magic != b"CHK" {
            return Err(LoadError::BadMagic(header.magic));
        }

        if header.version != CHUNK_LAYOUT_VERSION {
            return Err(LoadError::UnsupportedVersion(header.version));
        }

        Ok(header)
    }
}



#[cfg(test)]
mod test {
    use super::*;
    use crate::Memory64;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn new_and_load() {
        let mem = make_memory();

        // Create a new allocator.
        let allocator = Allocator::new(mem.clone(), 0, 16 /* chunk size */);

        // Load it from memory.
        let allocator = Allocator::load(mem.clone(), 0).unwrap();

        assert_eq!(allocator.chunk_size, 16);
        assert_eq!(
            allocator.head,
            core::mem::size_of::<AllocatorHeader>() as u64
        );

        // Load the first memory chunk.
        let chunk = Chunk::load(allocator.head, &mem).unwrap();
        assert_eq!(chunk.next, NULL);
    }

    #[test]
    fn allocate() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 0, 16 /* chunk size */).unwrap();

        allocator.allocate().unwrap();
        allocator.allocate().unwrap();
        allocator.allocate().unwrap();

        // Each allocation should push the `head` by `chunk_size`.

        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, header_len + 16 /*chunk size*/ * 3);
    }

    #[test]
    fn allocate_large() {
        // Allocate large chunks to verify that we are growing the memory.
        let mem = make_memory();
        assert_eq!(mem.size(), 0);

        let mut allocator =
            Allocator::new(mem.clone(), 0, WASM_PAGE_SIZE as u32 /* chunk size */).unwrap();
        assert_eq!(mem.size(), 1);

        allocator.allocate().unwrap();
        assert_eq!(mem.size(), 2);

        allocator.allocate().unwrap();
        assert_eq!(mem.size(), 3);

        allocator.allocate().unwrap();
        assert_eq!(mem.size(), 4);

        // Each allocation should push the `head` by `chunk_size`.
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(
            allocator.head,
            header_len + WASM_PAGE_SIZE /*chunk size*/ * 3
        );
        assert_eq!(allocator.num_allocations, 3);

        // Load and reload to verify that the data is the same.
        let mut allocator = Allocator::load(mem.clone(), 0).unwrap();
        assert_eq!(
            allocator.head,
            header_len + WASM_PAGE_SIZE /*chunk size*/ * 3
        );
        assert_eq!(allocator.num_allocations, 3);
    }

    #[test]
    fn allocate_deallocate() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 0, 16 /* chunk size */).unwrap();

        let chunk_addr = allocator.allocate().unwrap();
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, header_len + 16 /*chunk size*/);
        allocator.deallocate(chunk_addr);
        assert_eq!(allocator.head, header_len);
        assert_eq!(allocator.num_allocations, 0);

        // Load and reload to verify that the data is the same.
        let mut allocator = Allocator::load(mem.clone(), 0).unwrap();
        assert_eq!(allocator.head, header_len);
        assert_eq!(allocator.num_allocations, 0);
    }

    #[test]
    fn allocate_deallocate_2() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 0, 16 /* chunk size */).unwrap();

        let chunk_addr_1 = allocator.allocate().unwrap();
        let chunk_addr_2 = allocator.allocate().unwrap();

        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, chunk_addr_2 + 16 /*chunk size*/);
        allocator.deallocate(chunk_addr_2);
        assert_eq!(allocator.head, chunk_addr_2);

        let chunk_addr_3 = allocator.allocate().unwrap();
        assert_eq!(chunk_addr_3, chunk_addr_2);
        assert_eq!(allocator.head, chunk_addr_3 + 16 /*chunk size*/);
    }
}
