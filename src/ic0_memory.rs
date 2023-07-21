use crate::Memory;

#[derive(Clone, Copy, Default)]
pub struct Ic0StableMemory;

impl Memory for Ic0StableMemory {
    fn size(&self) -> u64 {
        // SAFETY: This is safe because of the ic0 api guarantees.
        unsafe { ic0::stable64_size() as u64 }
    }

    fn grow(&self, pages: u64) -> i64 {
        // SAFETY: This is safe because of the ic0 api guarantees.
        unsafe { ic0::stable64_grow(pages as i64) }
    }

    fn read(&self, offset: u64, dst: &mut [u8]) {
        // SAFETY: This is safe because of the ic0 api guarantees.
        unsafe { ic0::stable64_read(dst.as_ptr() as i64, offset as i64, dst.len() as i64) }
    }

    fn write(&self, offset: u64, src: &[u8]) {
        // SAFETY: This is safe because of the ic0 api guarantees.
        unsafe { ic0::stable64_write(offset as i64, src.as_ptr() as i64, src.len() as i64) }
    }
}
