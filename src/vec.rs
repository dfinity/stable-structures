//! This module implements a growable array in stable memory.
//!
//! # V1 layout
//!
//! ```text
//! ---------------------------------------- <- Address 0
//! Magic "SVC"            ↕ 3 bytes
//! ----------------------------------------
//! Layout version         ↕ 1 byte
//! ----------------------------------------
//! Number of entries = L  ↕ 8 bytes
//! ----------------------------------------
//! Max entry size         ↕ 4 bytes
//! ----------------------------------------
//! Fixed size flag        ↕ 1 byte
//! ----------------------------------------
//! Reserved space         ↕ 47 bytes
//! ---------------------------------------- <- Address 64
//! E_0                    ↕ SLOT_SIZE bytes
//! ----------------------------------------
//! E_1                    ↕ SLOT_SIZE bytes
//! ----------------------------------------
//! ...
//! ----------------------------------------
//! E_(L-1)                ↕ SLOT_SIZE bytes
//! ----------------------------------------
//! Unallocated space
//! ```
//!
//! The `SLOT_SIZE` constant depends on the item type. If the item
//! type sets the `BoundedStorable::IS_FIXED_SIZE` flag, the
//! `SLOT_SIZE` is equal to `BoundedStorable::MAX_SIZE`.  Otherwise,
//! the `SLOT_SIZE` is `BoundedStorable::MAX_SIZE` plus the number of
//! bytes required to represent integers up to
//! `BoundedStorable::MAX_SIZE`.
use crate::storable::bytes_to_store_size;
use crate::{
    read_u32, read_u64, safe_write, write_u32, write_u64, Address, BoundedStorable, GrowFailed,
    Memory,
};
use std::borrow::{Borrow, Cow};
use std::fmt;
use std::marker::PhantomData;

#[cfg(test)]
mod tests;

const MAGIC: [u8; 3] = *b"SVC"; // Short for "stable vector".
const LAYOUT_VERSION: u8 = 1;
/// The offset where the user data begins.
const DATA_OFFSET: u64 = 64;
/// The offset where the vector length resides.
const LEN_OFFSET: u64 = 4;

#[derive(Debug)]
struct HeaderV1 {
    magic: [u8; 3],
    version: u8,
    len: u64,
    max_size: u32,
    is_fixed_size: bool,
}

#[derive(PartialEq, Eq, Debug)]
pub enum InitError {
    /// The memory already contains another data structure.
    /// Use [Vec::new] to overwrite it.
    BadMagic([u8; 3]),
    /// The current version of [Vec] does not support the of the
    /// memory layout.
    IncompatibleVersion(u8),
    /// The vector type is not compatible with the current vector
    /// layout: MAX_SIZE and/or IS_FIXED_SIZE differ from the original
    /// initialization parameters.
    IncompatibleElementType,
    /// Failed to allocate memory for the vector.
    OutOfMemory,
}

impl fmt::Display for InitError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadMagic(magic) => {
                write!(fmt, "bad magic number {:?}, expected {:?}", magic, MAGIC)
            }
            Self::IncompatibleVersion(version)
            => write!(
                fmt,
                "unsupported layout version {}; supported version numbers are 1..={}",
                version, LAYOUT_VERSION
            ),
            Self::IncompatibleElementType =>
                write!(fmt, "either MAX_SIZE or IS_FIXED_SIZE of the element type do not match the persisted vector attributes"),
            Self::OutOfMemory => write!(fmt, "failed to allocate memory for vector metadata"),
        }
    }
}

impl std::error::Error for InitError {}

/// An implementation of growable arrays in stable memory.
pub struct Vec<T: BoundedStorable, M: Memory> {
    memory: M,
    _marker: PhantomData<T>,
}

impl<T: BoundedStorable, M: Memory> Vec<T, M> {
    /// Creates a new empty vector in the specified memory,
    /// overwriting any data structures the memory might have
    /// contained previously.
    ///
    /// Complexity: O(1)
    pub fn new(memory: M) -> Result<Self, GrowFailed> {
        let header = HeaderV1 {
            magic: MAGIC,
            version: LAYOUT_VERSION,
            len: 0,
            max_size: T::MAX_SIZE,
            is_fixed_size: T::IS_FIXED_SIZE,
        };
        Self::write_header(&header, &memory)?;
        Ok(Self {
            memory,
            _marker: PhantomData,
        })
    }

    /// Initializes a vector in the specified memory.
    ///
    /// Complexity: O(1)
    ///
    /// PRECONDITION: the memory is either empty or contains a valid
    /// stable vector.
    pub fn init(memory: M) -> Result<Self, InitError> {
        if memory.size() == 0 {
            return Self::new(memory).map_err(|_| InitError::OutOfMemory);
        }
        let header = Self::read_header(&memory);
        if header.magic != MAGIC {
            return Err(InitError::BadMagic(header.magic));
        }
        if header.version != LAYOUT_VERSION {
            return Err(InitError::IncompatibleVersion(header.version));
        }
        if header.max_size != T::MAX_SIZE || header.is_fixed_size != T::IS_FIXED_SIZE {
            return Err(InitError::IncompatibleElementType);
        }

        Ok(Self {
            memory,
            _marker: PhantomData,
        })
    }

    /// Returns the underlying memory instance.
    pub fn into_memory(self) -> M {
        self.memory
    }

    /// Returns true if the vector is empty.
    ///
    /// Complexity: O(1)
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of items in the vector.
    ///
    /// Complexity: O(1)
    pub fn len(&self) -> u64 {
        read_u64(&self.memory, Address::from(LEN_OFFSET))
    }

    /// Sets the item at the specified index to the specified value.
    ///
    /// Complexity: O(T::MAX_SIZE)
    ///
    /// PRECONDITION: index < self.len()
    pub fn set(&self, index: u64, item: &T) {
        assert!(index < self.len());

        let offset = DATA_OFFSET + slot_size::<T>() as u64 * index as u64;
        let bytes = item.to_bytes();
        let data_offset = self
            .write_entry_size(offset, bytes.len() as u32)
            .expect("unreachable: cannot fail to write to pre-allocated area");
        self.memory.write(data_offset, bytes.borrow());
    }

    /// Returns the item at the specified index.
    ///
    /// Complexity: O(T::MAX_SIZE)
    pub fn get(&self, index: u64) -> Option<T> {
        if index < self.len() {
            Some(self.read_entry(index))
        } else {
            None
        }
    }

    /// Adds a new item at the end of the vector.
    ///
    /// Complexity: O(T::MAX_SIZE)
    pub fn push(&self, item: &T) -> Result<(), GrowFailed> {
        let index = self.len() as u64;
        let offset = DATA_OFFSET + slot_size::<T>() as u64 * index;
        let bytes = item.to_bytes();
        let data_offset = self.write_entry_size(offset, bytes.len() as u32)?;
        safe_write(&self.memory, data_offset, bytes.borrow())?;
        // NB. We update the size only after we ensure that the data
        // write succeeded.
        self.set_len(index + 1);
        Ok(())
    }

    /// Removes the item at the end of the vector.
    ///
    /// Complexity: O(T::MAX_SIZE)
    pub fn pop(&self) -> Option<T> {
        let len = self.len();
        if len == 0 {
            return None;
        }
        let value = self.read_entry(len - 1);
        self.set_len(len - 1);
        Some(value)
    }

    pub fn iter(&self) -> Iter<'_, T, M> {
        Iter {
            vec: self,
            buf: vec![],
            pos: 0,
        }
    }

    /// Reads the item at the specified index without any bound checks.
    fn read_entry(&self, index: u64) -> T {
        let mut data = std::vec::Vec::new();
        self.read_entry_to(index, &mut data);
        T::from_bytes(Cow::Owned(data))
    }

    /// Reads the item at the specified index without any bound checks.
    fn read_entry_to(&self, index: u64, buf: &mut std::vec::Vec<u8>) {
        let offset = DATA_OFFSET + slot_size::<T>() as u64 * index as u64;
        let (data_offset, data_size) = self.read_entry_size(offset);
        buf.resize(data_size, 0);
        self.memory.read(data_offset, &mut buf[..]);
    }

    /// Sets the vector's length.
    fn set_len(&self, new_len: u64) {
        write_u64(&self.memory, Address::from(LEN_OFFSET), new_len);
    }

    /// Writes the size of the item at the specified offset.
    fn write_entry_size(&self, offset: u64, size: u32) -> Result<u64, GrowFailed> {
        debug_assert!(size <= T::MAX_SIZE);

        if T::IS_FIXED_SIZE {
            Ok(offset)
        } else if T::MAX_SIZE <= u8::MAX as u32 {
            safe_write(&self.memory, offset, &[size as u8; 1])?;
            Ok(offset + 1)
        } else if T::MAX_SIZE <= u16::MAX as u32 {
            safe_write(&self.memory, offset, &(size as u16).to_le_bytes())?;
            Ok(offset + 2)
        } else {
            safe_write(&self.memory, offset, &size.to_le_bytes())?;
            Ok(offset + 4)
        }
    }

    /// Reads the size of the entry at the specified offset.
    fn read_entry_size(&self, offset: u64) -> (u64, usize) {
        if T::IS_FIXED_SIZE {
            (offset, T::MAX_SIZE as usize)
        } else if T::MAX_SIZE <= u8::MAX as u32 {
            let mut size = [0u8; 1];
            self.memory.read(offset, &mut size);
            (offset + 1, size[0] as usize)
        } else if T::MAX_SIZE <= u16::MAX as u32 {
            let mut size = [0u8; 2];
            self.memory.read(offset, &mut size);
            (offset + 2, u16::from_le_bytes(size) as usize)
        } else {
            let size = read_u32(&self.memory, Address::from(offset));
            (offset + 4, size as usize)
        }
    }

    /// Write the layout header to the memory.
    fn write_header(header: &HeaderV1, memory: &M) -> Result<(), GrowFailed> {
        safe_write(memory, 0, &header.magic)?;
        memory.write(3, &[header.version; 1]);
        write_u64(memory, Address::from(4), header.len);
        write_u32(memory, Address::from(12), header.max_size);
        memory.write(16, &[if header.is_fixed_size { 1u8 } else { 0u8 }; 1]);
        Ok(())
    }

    /// Reads the header from the specified memory.
    ///
    /// PRECONDITION: memory.size() > 0
    fn read_header(memory: &M) -> HeaderV1 {
        debug_assert!(memory.size() > 0);

        let mut magic = [0u8; 3];
        let mut version = [0u8; 1];
        let mut is_fixed_size = [0u8; 1];
        memory.read(0, &mut magic);
        memory.read(3, &mut version);
        let len = read_u64(memory, Address::from(LEN_OFFSET));
        let max_size = read_u32(memory, Address::from(12));
        memory.read(16, &mut is_fixed_size);

        HeaderV1 {
            magic,
            version: version[0],
            len,
            max_size,
            is_fixed_size: is_fixed_size[0] != 0,
        }
    }

    fn to_vec(&self) -> std::vec::Vec<T> {
        self.iter().collect()
    }
}

impl<T: BoundedStorable + fmt::Debug, M: Memory> fmt::Debug for Vec<T, M> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_vec().fmt(fmt)
    }
}

fn slot_size<T: BoundedStorable>() -> u32 {
    T::MAX_SIZE + bytes_to_store_size::<T>()
}

pub struct Iter<'a, T, M>
where
    T: BoundedStorable,
    M: Memory,
{
    vec: &'a Vec<T, M>,
    buf: std::vec::Vec<u8>,
    pos: u64,
}

impl<T, M> Iterator for Iter<'_, T, M>
where
    T: BoundedStorable,
    M: Memory,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.vec.len() <= self.pos {
            return None;
        }

        self.vec.read_entry_to(self.pos, &mut self.buf);
        self.pos = self.pos.saturating_add(1);
        Some(T::from_bytes(Cow::Borrowed(&self.buf)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.vec.len().saturating_sub(self.pos) as usize, None)
    }

    fn count(self) -> usize {
        let n = self.vec.len().saturating_sub(self.pos);
        if n > usize::MAX as u64 {
            panic!(
                "The number of items in the vec {} does not fit into usize",
                n
            );
        }
        n as usize
    }

    fn nth(&mut self, n: usize) -> Option<T> {
        self.pos = self.pos.saturating_add(n as u64);
        self.next()
    }
}
