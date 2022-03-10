use crate::{Memory64, WASM_PAGE_SIZE};

const LAYOUT_VERSION: u8 = 1;

#[derive(Debug, PartialEq, Eq)]
pub enum WriteError {
    IndexFull(u32),
    GrowFailed { current: u64, delta: u64 },
    AddressSpaceOverflow,
}

type Ptr = u64;
const NULL: Ptr = 0;

#[derive(Debug)]
#[repr(packed)]
struct MemoryBlock {
    magic: [u8; 4],
    next: Ptr,
}

/// OPEN QUESTION: should we keep the free list sorted? Alternative to use a bitmap.
pub struct Allocator<M: Memory64> {
    addr: Ptr,
    block_size: u32,
    memory: M,
    head: Ptr,
}

#[repr(packed)]
struct AllocatorHeader {
    magic: [u8; 3],
    version: u8,
    block_size: u32,
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
    pub fn new(memory: M, block_size: u32, addr: Ptr) -> Self {
        println!("new allocator");
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        let block_addr = addr + header_len;

        // Start with only one block. No next.
        let header = AllocatorHeader {
            magic: *b"BTA", // btree allocator
            version: LAYOUT_VERSION,
            block_size,
            head: block_addr,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<AllocatorHeader>(),
            )
        };

        println!("writing allocator header to address {}", addr);
        write(&memory, addr, header_slice);

        // Start with only one block. No next.
        let block = MemoryBlock {
            magic: *b"MEMB", // BTree memory allocator.
            next: NULL,
        };

        let a = Self {
            addr,
            block_size: header.block_size,
            head: header.head,
            memory,
        };

        println!("saving first block to address {}", block_addr);
        // Store the block directly after the header.
        a.save_block(block_addr, block);
        a
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
            block_size: header.block_size,
            head: header.head,
        })
    }

    /// Allocates a block with `block_size`.
    pub fn allocate(&mut self) -> Ptr {
        // FIXME: grow the memory if we need to.
        println!("reading head");
        let head_block = self.read(self.head);
        println!("done.");

        let new_block_addr = self.head;

        if head_block.next != NULL {
            // This block is now the new head.
            let new_head_addr = head_block.next;

            // Read the next block and update the pointer.
            println!("read");
            let mut new_head = self.read(new_head_addr);
            println!("done");
            self.save_block(new_head_addr, new_head);

            self.head = new_head_addr;

            // TODO: save to disk?
        } else {
            // There is no next block. Shift everything by block size.
            self.head += self.block_size as u64;

            // Write new block to that location.
            let block = MemoryBlock {
                magic: *b"MEMB", // BTree memory allocator.
                next: NULL,
            };

            self.save_block(self.head, block);
        }

        new_block_addr
    }

    pub fn deallocate(&mut self, address: Ptr) {
        println!("deallocating address {}", address);
        // Assume that address is valid (was returned in `allocate` before).
        //if address < self.head {
        // address becomes the new head.
        let block = MemoryBlock {
            magic: *b"MEMB", // BTree memory allocator.
            next: self.head,
        };

        self.head = address;

        self.save_block(address, block);
        //self.save(); FIXME
        //}
    }

    fn read(&self, address: Ptr) -> MemoryBlock {
        let mut header: MemoryBlock = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<MemoryBlock>(),
            )
        };

        self.memory.read(address, header_slice);

        if &header.magic != b"MEMB" {
            panic!(
                "bad memory header magic. Found {:?}, expected {:?}",
                header.magic, b"MEMB"
            );
        }

        header
    }

    fn save_block(&self, address: Ptr, block: MemoryBlock) {
        let block_slice = unsafe {
            core::slice::from_raw_parts(
                &block as *const _ as *const u8,
                core::mem::size_of::<MemoryBlock>(),
            )
        };

        write(&self.memory, address, block_slice).unwrap();
    }

    pub fn save(&self) {
        let header = AllocatorHeader {
            magic: *b"BTA", // btree allocator
            version: LAYOUT_VERSION,
            block_size: self.block_size,
            head: self.head,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<AllocatorHeader>(),
            )
        };

        println!("Saving allocator to address: {}", self.addr);
        write(&self.memory, self.addr, header_slice).unwrap();
    }

    // How much space is currently being used.
    //fn size(&self) -> u64 {
    //     self.header_addr
    //}
}

// TODO: move this into a common place?
fn write(memory: &impl Memory64, offset: u64, bytes: &[u8]) -> Result<(), WriteError> {
    let last_byte = offset
        .checked_add(bytes.len() as u64)
        .ok_or(WriteError::AddressSpaceOverflow)?;
    let size_pages = memory.size();
    let size_bytes = size_pages
        .checked_mul(WASM_PAGE_SIZE)
        .ok_or(WriteError::AddressSpaceOverflow)?;
    if size_bytes < last_byte {
        let diff_bytes = last_byte - size_bytes;
        let diff_pages = diff_bytes
            .checked_add(WASM_PAGE_SIZE - 1)
            .ok_or(WriteError::AddressSpaceOverflow)?
            / WASM_PAGE_SIZE;
        if memory.grow(diff_pages) == -1 {
            return Err(WriteError::GrowFailed {
                current: size_pages,
                delta: diff_pages,
            });
        }
    }
    memory.write(offset, bytes);
    Ok(())
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
        let allocator = Allocator::new(mem.clone(), 16 /* block size */, 0);

        // Load it from memory.
        let allocator = Allocator::load(mem, 0).unwrap();

        assert_eq!(allocator.block_size, 16);
        assert_eq!(
            allocator.head,
            core::mem::size_of::<AllocatorHeader>() as u64
        );

        // Load the first memory block.
        let block = allocator.read(allocator.head);
        assert_eq!(block.next, NULL);
    }

    #[test]
    fn allocate() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 16 /* block size */, 0);

        allocator.allocate();
        allocator.allocate();
        allocator.allocate();

        // Each allocation should push the `head` by `block_size`.

        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, header_len + 16 /*block size*/ * 3);
    }

    #[test]
    fn allocate_deallocate() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 16 /* block size */, 0);

        let block_addr = allocator.allocate();
        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, header_len + 16 /*block size*/);
        allocator.deallocate(block_addr);
        assert_eq!(allocator.head, header_len);
    }

    #[test]
    fn allocate_deallocate_2() {
        let mem = make_memory();

        let mut allocator = Allocator::new(mem.clone(), 16 /* block size */, 0);

        let block_addr_1 = allocator.allocate();
        let block_addr_2 = allocator.allocate();

        let header_len = core::mem::size_of::<AllocatorHeader>() as u64;
        assert_eq!(allocator.head, block_addr_2 + 16 /*block size*/);
        allocator.deallocate(block_addr_2);
        assert_eq!(allocator.head, block_addr_2);

        let block_addr_3 = allocator.allocate();
        assert_eq!(block_addr_3, block_addr_2);
        assert_eq!(allocator.head, block_addr_3 + 16 /*block size*/);
    }
}
