use crate::btree::{write, WriteError};
use crate::{Memory64, WASM_PAGE_SIZE};

const LAYOUT_VERSION: u8 = 1;

type Ptr = u64;
const NULL: Ptr = 0;

#[derive(Debug)]
#[repr(packed)]
struct Chunk {
    magic: [u8; 4],
    next: Ptr,
}

/// A free list constant-size chunk allocator.
pub struct Allocator<M: Memory64> {
    addr: Ptr,
    chunk_size: u32,
    memory: M,
    head: Ptr,
}

#[repr(packed)]
struct AllocatorHeader {
    magic: [u8; 3],
    version: u8,
    chunk_size: u32,
    head: Ptr,
}

#[derive(Debug)]
pub enum LoadError {
    MemoryEmpty,
    BadMagic([u8; 3]),
    UnsupportedVersion(u8),
}

impl<M: Memory64> Allocator<M> {
    // Assume that everything after `head` is free.
    pub fn new(memory: M, chunk_size: u32, addr: Ptr) -> Result<Self, WriteError> {
        println!("new allocator");
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        let head_addr = addr + header_len;

        // Start with only one chunk. No next.
        let chunk = Chunk {
            magic: *b"CHNK",
            next: NULL,
        };

        let allocator = Self {
            addr,
            chunk_size,
            head: head_addr,
            memory,
        };

        println!("saving first chunk to address {}", head_addr);
        // Store the chunk directly after the header.
        allocator.save_chunk(head_addr, chunk)?;
        allocator.save()?;

        Ok(allocator)
    }

    pub fn load(memory: M, address: Ptr) -> Result<Self, LoadError> {
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
        memory.read(address, header_slice);
        if &header.magic != b"BTA" {
            println!("magic found: {:?}", header.magic);
            println!("magic expected: {:?}", b"BTA");
            return Err(LoadError::BadMagic(header.magic));
        }
        if header.version != LAYOUT_VERSION {
            return Err(LoadError::UnsupportedVersion(header.version));
        }
        Ok(Self {
            addr: address,
            memory,
            chunk_size: header.chunk_size,
            head: header.head,
        })
    }

    /// Allocates a chunk with `chunk_size`.
    pub fn allocate(&mut self) -> Ptr {
        // FIXME: grow the memory if we need to.
        println!("reading head");
        let head_chunk = self.read(self.head);
        println!("done.");

        let new_chunk_addr = self.head;

        if head_chunk.next != NULL {
            // This chunk is now the new head.
            let new_head_addr = head_chunk.next;

            // Read the next chunk and update the pointer.
            println!("read");
            let mut new_head = self.read(new_head_addr);
            println!("done");
            self.save_chunk(new_head_addr, new_head).unwrap();

            self.head = new_head_addr;

            // TODO: save to disk?
        } else {
            // There is no next chunk. Shift everything by chunk size.
            self.head += self.chunk_size as u64;

            // Write new chunk to that location.
            let chunk = Chunk {
                magic: *b"CHNK", // BTree memory allocator.
                next: NULL,
            };

            self.save_chunk(self.head, chunk);
        }

        new_chunk_addr
    }

    pub fn deallocate(&mut self, address: Ptr) {
        println!("deallocating address {}", address);
        // Assume that address is valid (was returned in `allocate` before).
        //if address < self.head {
        // address becomes the new head.
        let chunk = Chunk {
            magic: *b"CHNK", // BTree memory allocator.
            next: self.head,
        };

        self.head = address;

        self.save_chunk(address, chunk);
        //self.save(); FIXME
        //}
    }

    fn read(&self, address: Ptr) -> Chunk {
        let mut header: Chunk = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<Chunk>(),
            )
        };

        self.memory.read(address, header_slice);

        if &header.magic != b"CHNK" {
            panic!(
                "bad memory header magic. Found {:?}, expected {:?}",
                header.magic, b"CHNK"
            );
        }

        header
    }

    fn save_chunk(&self, address: Ptr, chunk: Chunk) -> Result<(), WriteError> {
        let chunk_slice = unsafe {
            core::slice::from_raw_parts(
                &chunk as *const _ as *const u8,
                core::mem::size_of::<Chunk>(),
            )
        };

        write(&self.memory, address, chunk_slice)
    }

    pub fn save(&self) -> Result<(), WriteError> {
        let header = AllocatorHeader {
            magic: *b"BTA", // btree allocator
            version: LAYOUT_VERSION,
            chunk_size: self.chunk_size,
            head: self.head,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<AllocatorHeader>(),
            )
        };

        println!("Saving node to address: {}", self.addr);
        write(&self.memory, self.addr, header_slice)
    }

    // How much space is currently being used.
    //fn size(&self) -> u64 {
    //     self.header_addr
    //}
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
        let allocator = Allocator::new(mem.clone(), 16 /* chunk size */, 0);

        // Load it from memory.
        let allocator = Allocator::load(mem, 0).unwrap();

        assert_eq!(allocator.chunk_size, 16);
        assert_eq!(
            allocator.head,
            core::mem::size_of::<AllocatorHeader>() as u64
        );

        // Load the first memory chunk.
        let chunk = allocator.read(allocator.head);
        assert_eq!(chunk.next, NULL);
    }

    #[test]
    fn allocate() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 16 /* chunk size */, 0).unwrap();

        allocator.allocate();
        allocator.allocate();
        allocator.allocate();

        // Each allocation should push the `head` by `chunk_size`.

        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, header_len + 16 /*chunk size*/ * 3);
    }

    #[test]
    fn allocate_deallocate() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 16 /* chunk size */, 0).unwrap();

        let chunk_addr = allocator.allocate();
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, header_len + 16 /*chunk size*/);
        allocator.deallocate(chunk_addr);
        assert_eq!(allocator.head, header_len);
    }

    #[test]
    fn allocate_deallocate_2() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 16 /* chunk size */, 0).unwrap();

        let chunk_addr_1 = allocator.allocate();
        let chunk_addr_2 = allocator.allocate();

        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, chunk_addr_2 + 16 /*chunk size*/);
        allocator.deallocate(chunk_addr_2);
        assert_eq!(allocator.head, chunk_addr_2);

        let chunk_addr_3 = allocator.allocate();
        assert_eq!(chunk_addr_3, chunk_addr_2);
        assert_eq!(allocator.head, chunk_addr_3 + 16 /*chunk size*/);
    }
}
