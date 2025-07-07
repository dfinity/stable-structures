#![doc = include_str!("../README.md")]
mod base_vec;
pub mod btreemap;
pub mod cell;
pub use cell::{Cell as StableCell, Cell};
pub mod btreeset;
pub mod file_mem;
#[cfg(target_arch = "wasm32")]
mod ic0_memory; // Memory API for canisters.
pub mod log;
pub mod memory_manager;
pub mod min_heap;
pub mod reader;
pub mod storable;
#[cfg(test)]
mod tests;
mod types;
pub mod vec;
pub mod vec_mem;
pub mod writer;

pub use btreemap::{BTreeMap, BTreeMap as StableBTreeMap};
pub use btreeset::{BTreeSet, BTreeSet as StableBTreeSet};
pub use file_mem::FileMemory;
#[cfg(target_arch = "wasm32")]
pub use ic0_memory::Ic0StableMemory;
pub use log::{Log as StableLog, Log};
pub use min_heap::{MinHeap, MinHeap as StableMinHeap};
use std::error;
use std::fmt::{Display, Formatter};
use std::mem::MaybeUninit;
pub use storable::Storable;
use types::Address;
pub use vec::{Vec as StableVec, Vec};
pub use vec_mem::VectorMemory;

#[cfg(target_arch = "wasm32")]
pub type DefaultMemoryImpl = Ic0StableMemory;

#[cfg(not(target_arch = "wasm32"))]
pub type DefaultMemoryImpl = VectorMemory;

const WASM_PAGE_SIZE: u64 = 65536;

/// The maximum number of stable memory pages a canister can address.
pub const MAX_PAGES: u64 = u64::MAX / WASM_PAGE_SIZE;

/// Abstraction over a WebAssembly-style linear memory (e.g., stable memory).
///
/// Implementations are expected to mirror WebAssembly semantics:
/// out-of-bounds accesses will cause a panic (in native) or trap (in Wasm).
pub trait Memory {
    /// Returns the current size of the memory in WebAssembly pages.
    ///
    /// One WebAssembly page is 64 KiB.
    fn size(&self) -> u64;

    /// Grows the memory by `pages` pages filled with zeroes.
    ///
    /// Returns the previous size in pages on success, or -1 if the
    /// memory could not be grown.
    fn grow(&self, pages: u64) -> i64;

    /// Copies `dst.len()` bytes from memory starting at `offset` into `dst`.
    ///
    /// Panics or traps if the read would go out of bounds.
    fn read(&self, offset: u64, dst: &mut [u8]);

    /// Unsafe variant of `read` for advanced use.
    ///
    /// Copies `count` bytes from memory starting at `offset` into the
    /// raw pointer `dst`. Initializes the destination before reading.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `dst` points to valid writable memory of at least `count` bytes.
    /// - The memory range `dst..dst+count` does not overlap with `self`.
    ///
    /// Panics or traps if the read would go out of bounds.
    #[inline]
    unsafe fn read_unsafe(&self, offset: u64, dst: *mut u8, count: usize) {
        // Initialize the buffer to make the slice valid.
        std::ptr::write_bytes(dst, 0, count);
        let slice = std::slice::from_raw_parts_mut(dst, count);
        self.read(offset, slice)
    }

    /// Copies `src.len()` bytes from `src` into memory starting at `offset`.
    ///
    /// Panics or traps if the write would go out of bounds.
    fn write(&self, offset: u64, src: &[u8]);
}

/// Copies `count` bytes of data starting from `addr` out of the stable memory into `dst`.
///
/// Callers are allowed to pass vectors in any state (e.g. empty vectors).
/// After the method returns, `dst.len() == count`.
/// This method is an alternative to `read` which does not require initializing a buffer and may
/// therefore be faster.
#[inline]
fn read_to_vec<M: Memory>(m: &M, addr: Address, dst: &mut std::vec::Vec<u8>, count: usize) {
    dst.clear();
    dst.reserve_exact(count);
    unsafe {
        m.read_unsafe(addr.get(), dst.as_mut_ptr(), count);
        // SAFETY: read_unsafe guarantees to initialize the first `count` bytes
        dst.set_len(count);
    }
}

/// A helper function that reads a single 32bit integer encoded as
/// little-endian from the specified memory at the specified offset.
fn read_u32<M: Memory>(m: &M, addr: Address) -> u32 {
    let mut buf: [u8; 4] = [0; 4];
    m.read(addr.get(), &mut buf);
    u32::from_le_bytes(buf)
}

/// A helper function that reads a single 64bit integer encoded as
/// little-endian from the specified memory at the specified offset.
fn read_u64<M: Memory>(m: &M, addr: Address) -> u64 {
    let mut buf: [u8; 8] = [0; 8];
    m.read(addr.get(), &mut buf);
    u64::from_le_bytes(buf)
}

/// Reads `count` u64 values from memory starting at `addr` using a single memory read.
fn read_u64_vec<M: Memory>(m: &M, addr: Address, count: usize) -> std::vec::Vec<u64> {
    let byte_len = count * 8;
    let mut buf = std::vec::Vec::with_capacity(byte_len);
    read_to_vec(m, addr, &mut buf, byte_len);

    let mut result = std::vec::Vec::with_capacity(count);
    let mut chunks = buf.chunks_exact(8);

    unsafe {
        for chunk in &mut chunks {
            // SAFETY: each chunk has length 8
            let bytes: [u8; 8] = chunk.try_into().unwrap_unchecked();
            result.push(u64::from_le_bytes(bytes));
        }
    }

    result
}

/// Writes a single 32-bit integer encoded as little-endian.
fn write_u32<M: Memory>(m: &M, addr: Address, val: u32) {
    write(m, addr.get(), &val.to_le_bytes());
}

/// Writes a single 64-bit integer encoded as little-endian.
fn write_u64<M: Memory>(m: &M, addr: Address, val: u64) {
    write(m, addr.get(), &val.to_le_bytes());
}

#[derive(Debug, PartialEq, Eq)]
pub struct GrowFailed {
    current_size: u64,
    delta: u64,
}

impl Display for GrowFailed {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Failed to grow memory: current size={}, delta={}",
            self.current_size, self.delta
        )
    }
}

impl error::Error for GrowFailed {}

/// Writes the bytes at the specified offset, growing the memory size if needed.
fn safe_write<M: Memory>(memory: &M, offset: u64, bytes: &[u8]) -> Result<(), GrowFailed> {
    let last_byte = offset
        .checked_add(bytes.len() as u64)
        .expect("Address space overflow");

    let size_pages = memory.size();
    let size_bytes = size_pages
        .checked_mul(WASM_PAGE_SIZE)
        .expect("Address space overflow");

    if size_bytes < last_byte {
        let diff_bytes = last_byte - size_bytes;
        let diff_pages = diff_bytes
            .checked_add(WASM_PAGE_SIZE - 1)
            .expect("Address space overflow")
            / WASM_PAGE_SIZE;
        if memory.grow(diff_pages) == -1 {
            return Err(GrowFailed {
                current_size: size_pages,
                delta: diff_pages,
            });
        }
    }
    memory.write(offset, bytes);
    Ok(())
}

/// Like [safe_write], but panics if the memory.grow fails.
fn write<M: Memory>(memory: &M, offset: u64, bytes: &[u8]) {
    if let Err(GrowFailed {
        current_size,
        delta,
    }) = safe_write(memory, offset, bytes)
    {
        panic!(
            "Failed to grow memory from {} pages to {} pages (delta = {} pages).",
            current_size,
            current_size + delta,
            delta
        );
    }
}

/// Reads a struct from memory.
fn read_struct<T, M: Memory>(addr: Address, memory: &M) -> T {
    let mut value = MaybeUninit::<T>::uninit();
    unsafe {
        memory.read_unsafe(
            addr.get(),
            value.as_mut_ptr() as *mut u8,
            core::mem::size_of::<T>(),
        );
        value.assume_init()
    }
}

/// Writes a struct to memory.
fn write_struct<T, M: Memory>(t: &T, addr: Address, memory: &M) {
    let slice = unsafe {
        core::slice::from_raw_parts(t as *const _ as *const u8, core::mem::size_of::<T>())
    };

    write(memory, addr.get(), slice)
}

/// RestrictedMemory creates a limited view of another memory.  This
/// allows one to divide the main memory into non-intersecting ranges
/// and use different layouts in each region.
#[derive(Clone)]
pub struct RestrictedMemory<M: Memory> {
    page_range: core::ops::Range<u64>,
    memory: M,
}

impl<M: Memory> RestrictedMemory<M> {
    pub fn new(memory: M, page_range: core::ops::Range<u64>) -> Self {
        assert!(page_range.end <= MAX_PAGES);
        Self { memory, page_range }
    }
}

impl<M: Memory> Memory for RestrictedMemory<M> {
    fn size(&self) -> u64 {
        let base_size = self.memory.size();
        if base_size < self.page_range.start {
            0
        } else if base_size > self.page_range.end {
            self.page_range.end - self.page_range.start
        } else {
            base_size - self.page_range.start
        }
    }

    fn grow(&self, delta: u64) -> i64 {
        let base_size = self.memory.size();
        if base_size < self.page_range.start {
            self.memory
                .grow(self.page_range.start - base_size + delta)
                .min(0)
        } else if base_size >= self.page_range.end {
            if delta == 0 {
                (self.page_range.end - self.page_range.start) as i64
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
                    r - self.page_range.start as i64
                }
            }
        }
    }

    fn read(&self, offset: u64, dst: &mut [u8]) {
        self.memory
            .read(self.page_range.start * WASM_PAGE_SIZE + offset, dst)
    }

    unsafe fn read_unsafe(&self, offset: u64, dst: *mut u8, count: usize) {
        self.memory
            .read_unsafe(self.page_range.start * WASM_PAGE_SIZE + offset, dst, count)
    }

    fn write(&self, offset: u64, src: &[u8]) {
        self.memory
            .write(self.page_range.start * WASM_PAGE_SIZE + offset, src)
    }
}
