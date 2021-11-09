pub mod allocator;
use allocator::Allocator;
#[cfg(target_arch = "wasm32")]
mod ic0_api;
pub mod hashmap;
pub use hashmap::HashMap as HashMap;
pub mod log;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod log_tests;
pub mod vec_mem;

const WASM_PAGE_SIZE: u32 = 65536;

pub trait Memory {
    /// Returns the current size of the stable memory in WebAssembly
    /// pages. (One WebAssembly page is 64Ki bytes.)
    fn size(&self) -> u32;

    /// Tries to grow the memory by new_pages many pages containing
    /// zeroes.  If successful, returns the previous size of the
    /// memory (in pages).  Otherwise, returns -1.
    fn grow(&self, pages: u32) -> i32;

    /// Copies the data referred to by offset out of the stable memory
    /// and replaces the corresponding bytes in dst.
    fn read(&self, offset: u32, dst: &mut [u8]);

    /// Copies the data referred to by src and replaces the
    /// corresponding segment starting at offset in the stable memory.
    fn write(&self, offset: u32, src: &[u8]);
}

/// A helper function that reads a single 32bit integer encoded as
/// little-endian from the specified memory at the specified offset.
fn read_u32<M: Memory>(m: &M, offset: u32) -> u32 {
    let mut buf: [u8; 4] = [0; 4];
    m.read(offset, &mut buf);
    u32::from_le_bytes(buf)
}

fn write_u32<M: Memory>(m: &M, offset: u32, n: u32) {
    m.write(offset, &n.to_le_bytes());
}


/// RestrictedMemory creates a limited view of another memory.  This
/// allows one to divide the main memory into non-intersecting ranges
/// and use different layouts in each region.
pub struct RestrictedMemory<M: Memory> {
    page_range: core::ops::Range<u32>,
    memory: M,
}

impl<M: Memory> RestrictedMemory<M> {
    pub fn new(memory: M, page_range: core::ops::Range<u32>) -> Self {
        assert!(page_range.end < u32::MAX / WASM_PAGE_SIZE);
        Self { memory, page_range }
    }
}

impl<M: Memory> Memory for RestrictedMemory<M> {
    fn size(&self) -> u32 {
        let base_size = self.memory.size();
        if base_size < self.page_range.start {
            0
        } else if base_size > self.page_range.end {
            self.page_range.end - self.page_range.start
        } else {
            base_size - self.page_range.start
        }
    }

    fn grow(&self, delta: u32) -> i32 {
        let base_size = self.memory.size();
        if base_size < self.page_range.start {
            self.memory
                .grow(self.page_range.start - base_size + delta)
                .min(0)
        } else if base_size >= self.page_range.end {
            if delta == 0 {
                (self.page_range.end - self.page_range.start) as i32
            } else {
                -1
            }
        } else {
            let pages_left = self.page_range.end - base_size;
            if pages_left < delta {
                -1
            } else {
                let r = self.memory.grow(delta);
                if r < 0 {
                    r
                } else {
                    r - self.page_range.start as i32
                }
            }
        }
    }

    fn read(&self, offset: u32, dst: &mut [u8]) {
        self.memory
            .read(self.page_range.start * WASM_PAGE_SIZE + offset, dst)
    }

    fn write(&self, offset: u32, src: &[u8]) {
        self.memory
            .write(self.page_range.start * WASM_PAGE_SIZE + offset, src)
    }
}


/// Root data is data stored in the memory and a pointer to this data is stored at the
/// special address of zero. This is particularly useful during an upgrade. The root
/// data can consist of metadata used to recover the data structures that were previously
/// declared.
pub fn write_root_data<M: Memory, A: Allocator>(memory: &M, allocator: &A, root_data: &[u8]) {
    let old_root_address = read_u32(memory, 0);
    let old_root_size = read_u32(memory, 4);

    if old_root_address != 0 && old_root_size > 0 {
        // Deallocate previous root data.
        allocator.deallocate(old_root_address, old_root_size);
    }

    let root_address = allocator.allocate(root_data.len() as u32).unwrap();

    memory.write(root_address, root_data);

    write_u32(memory, 0, root_address);
    write_u32(memory, 4, root_data.len() as u32);
}

pub fn read_root_data<M: Memory>(memory: &M) -> Option<Vec<u8>> {
    if memory.size() == 0 {
        return None;
    }

    let root_address = read_u32(memory, 0);
    let root_size = read_u32(memory, 4);

    if root_address == 0 || root_size == 0 {
        return None;
    }

    let mut root_data = vec![0; root_size as usize];
    memory.read(root_address, &mut root_data);
    Some(root_data)
}
