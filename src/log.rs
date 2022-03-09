use crate::{Memory, WASM_PAGE_SIZE};
use std::cell::Cell;

pub const LAYOUT_VERSION: u8 = 1;

#[repr(packed)]
struct Header {
    magic: [u8; 3],
    version: u8,
    max_entries: u32,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AllocError {
    GrowFailed { current: u64, delta: u64 },
    AddressSpaceOverflow,
}

#[derive(Debug, PartialEq, Eq)]
pub enum LoadError {
    MemoryEmpty,
    BadMagic([u8; 3]),
    UnsupportedVersion(u8),
}

#[derive(Debug, PartialEq, Eq)]
pub enum WriteError {
    IndexFull(u32),
    GrowFailed { current: u64, delta: u64 },
    AddressSpaceOverflow,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NoSuchEntry;

pub struct StableLog<M: Memory> {
    max_entries: u32,
    num_entries: Cell<u32>,
    index_offset: u32,
    entries_offset: u32,
    memory: M,
}

impl<M: Memory> StableLog<M> {
    pub fn new(memory: M, max_entries: u32) -> Result<Self, AllocError> {
        let header_len = core::mem::size_of::<Header>() as u32;

        let index_len = max_entries
            .checked_mul(4)
            .ok_or(AllocError::AddressSpaceOverflow)?
            .checked_add(4)
            .ok_or(AllocError::AddressSpaceOverflow)?;

        let header = Header {
            magic: *b"LOG",
            version: LAYOUT_VERSION,
            max_entries,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<Header>(),
            )
        };

        if memory.size() < 1 {
            if memory.grow(1) == -1 {
                return Err(AllocError::GrowFailed {
                    current: 0,
                    delta: 1,
                });
            }
        }
        memory.write(0, header_slice);

        Ok(Self {
            max_entries,
            num_entries: Cell::new(0),
            index_offset: header_len,
            entries_offset: header_len + index_len,
            memory,
        })
    }

    pub fn load(memory: M) -> Result<Self, LoadError> {
        let mut header: Header = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<Header>(),
            )
        };
        if memory.size() == 0 {
            return Err(LoadError::MemoryEmpty);
        }
        memory.read(0, header_slice);
        if &header.magic != b"LOG" {
            return Err(LoadError::BadMagic(header.magic));
        }
        if header.version != LAYOUT_VERSION {
            return Err(LoadError::UnsupportedVersion(header.version));
        }
        let index_offset = core::mem::size_of::<Header>() as u32;
        let num_entries = crate::read_u32(&memory, index_offset as u64);
        Ok(Self {
            max_entries: header.max_entries,
            num_entries: Cell::new(num_entries),
            index_offset,
            entries_offset: index_offset + header.max_entries * 4 + 4,
            memory,
        })
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        self.num_entries.get() as usize
    }

    pub fn max_len(&self) -> usize {
        self.max_entries as usize
    }

    pub fn get_entry(&self, idx: u32) -> Result<Vec<u8>, NoSuchEntry> {
        let mut buf = vec![];
        self.read_entry(idx, &mut buf)?;
        Ok(buf)
    }

    /// Reads the contents of the entry with the specified index into
    /// a byte vector.  The vector is resized to the entry size.
    pub fn read_entry(&self, idx: u32, buf: &mut Vec<u8>) -> Result<(), NoSuchEntry> {
        let (offset, len) = self.entry_meta(idx)?;
        if buf.capacity() < len as usize {
            buf.reserve(len as usize - buf.len());
        }
        // Safety: the check above verifies that the vector has enough
        // capacity, and memory.read guarantees to fill the whole
        // buffer.
        unsafe {
            buf.set_len(len as usize);
        }
        self.memory.read((self.entries_offset + offset) as u64, buf);
        Ok(())
    }

    /// Appends a new entry to the log.
    /// If successful, returns the index of the entry.
    ///
    /// Postcondition: Ok(i) = log.append_entry(X) ⇒ log.get_entry(i) = X
    pub fn append_entry(&self, bytes: &[u8]) -> Result<u32, WriteError> {
        let n = self.num_entries.get();
        if n == self.max_entries {
            return Err(WriteError::IndexFull(n));
        }

        let offset = if n == 0 {
            0
        } else {
            crate::read_u32(&self.memory, self.index_entry_offset(n - 1) as u64)
        };

        let new_offset = offset
            .checked_add(bytes.len() as u32)
            .ok_or(WriteError::AddressSpaceOverflow)?;

        let entry_offset = self
            .entries_offset
            .checked_add(offset)
            .ok_or(WriteError::AddressSpaceOverflow)?;

        self.write(entry_offset, bytes)?;
        self.write(self.index_offset, &(n + 1).to_le_bytes())?;
        self.write(self.index_entry_offset(n), &new_offset.to_le_bytes())?;
        self.num_entries.set(n + 1);
        Ok(n)
    }

    pub fn entry_meta(&self, idx: u32) -> Result<(u32, u32), NoSuchEntry> {
        if self.num_entries.get() <= idx {
            return Err(NoSuchEntry);
        }
        if idx == 0 {
            Ok((
                0,
                crate::read_u32(&self.memory, self.index_entry_offset(0) as u64),
            ))
        } else {
            let offset = crate::read_u32(&self.memory, self.index_entry_offset(idx - 1) as u64);
            let next = crate::read_u32(&self.memory, self.index_entry_offset(idx) as u64);
            Ok((offset, next - offset))
        }
    }

    fn index_entry_offset(&self, idx: u32) -> u32 {
        self.index_offset + idx * 4 + 4
    }

    fn write(&self, offset: u32, bytes: &[u8]) -> Result<(), WriteError> {
        let last_byte = offset
            .checked_add(bytes.len() as u32)
            .ok_or(WriteError::AddressSpaceOverflow)?;
        let size_pages = self.memory.size();
        let size_bytes = size_pages
            .checked_mul(WASM_PAGE_SIZE)
            .ok_or(WriteError::AddressSpaceOverflow)?;
        if size_bytes < last_byte as u64 {
            let diff_bytes = last_byte as u64 - size_bytes;
            let diff_pages = diff_bytes
                .checked_add(WASM_PAGE_SIZE - 1)
                .ok_or(WriteError::AddressSpaceOverflow)?
                / WASM_PAGE_SIZE;
            if self.memory.grow(diff_pages as u64) == -1 {
                return Err(WriteError::GrowFailed {
                    current: size_pages,
                    delta: diff_pages,
                });
            }
        }
        self.memory.write(offset as u64, bytes);
        Ok(())
    }
}
