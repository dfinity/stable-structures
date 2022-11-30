use std::marker::PhantomData;

use crate::{
    read_struct, read_u32,
    types::{Address, Bytes},
    write_struct, write_u32, BoundedStorable, Memory, WASM_PAGE_SIZE,
};

const LAYOUT_VERSION: u8 = 1;
const MAGIC: &[u8; 3] = b"VEC";

/// Memory layout:
///
/// T::fixed_value_size = true
/// +--------------------------------------+
/// | header | val | val | val | val | ... |
/// +--------------------------------------+
///
/// T::fixed_value_size = false
/// +------------------------------------------+
/// | header | [size; val] | [size; val] | ... |
/// +------------------------------------------+
/// size: u32
///
/// Returns the pointer to the entry (read: not necessarily the value).
pub struct Vec<M, T> {
    memory: M,
    max_value_size: u64,
    base: Address,

    len: usize,

    // A marker to communicate to the Rust compiler that we own these types.
    _phantom: PhantomData<T>,
}

#[repr(packed)]
struct StableVecHeader {
    magic: [u8; 3],
    version: u8,
    max_value_size: u64,
    fixed_value_size: bool,
    len: usize,
    // Additional space reserved to add new fields without breaking backward-compatibility.
    _buffer: [u8; 24],
}

impl StableVecHeader {
    fn size() -> Bytes {
        Bytes::from(core::mem::size_of::<Self>() as u64)
    }
}

impl<M: Memory, T: BoundedStorable> Vec<M, T> {
    const ENTRY_SIZE: usize = (T::MAX_SIZE + if T::FIXED_SIZE { 0 } else { 4 }) as usize;

    #[must_use]
    pub fn new(memory: M) -> Self {
        Self::new_with_sizes(memory, T::MAX_SIZE as u64)
    }

    #[must_use]
    pub fn new_with_sizes(memory: M, max_value_size: u64) -> Self {
        let v = Self {
            memory,
            max_value_size,
            base: Address::from(0) + StableVecHeader::size(),
            len: 0,
            _phantom: PhantomData,
        };

        v.save();
        v
    }

    pub fn load(memory: M) -> Self {
        Self::load_with_sizes(memory, T::MAX_SIZE as u64)
    }

    pub fn load_with_sizes(memory: M, max_value_size: u64) -> Self {
        // Read the header from memory.
        let header: StableVecHeader = read_struct(Address::from(0), &memory);
        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        assert_eq!(header.version, LAYOUT_VERSION, "Unsupported version.");
        assert_eq!(header.fixed_value_size, T::FIXED_SIZE);
        let expected_value_size = header.max_value_size;
        assert!(
            max_value_size <= expected_value_size,
            "max_value_size must be <= {}",
            expected_value_size
        );

        Self {
            memory,
            max_value_size: header.max_value_size,
            base: Address::from(0) + StableVecHeader::size(),
            len: header.len,
            _phantom: PhantomData,
        }
    }

    fn save(&self) {
        let header = StableVecHeader {
            magic: *MAGIC,
            version: LAYOUT_VERSION,
            max_value_size: self.max_value_size,
            fixed_value_size: T::FIXED_SIZE,
            len: self.len,
            _buffer: [0; 24],
        };

        write_struct(&header, Address::from(0), &self.memory);
    }

    pub fn clear(&mut self) {
        self.len = 0;
        self.save();
    }

    fn index_to_entry_addr(&self, index: usize) -> Address {
        self.base + Bytes::from((Self::ENTRY_SIZE * index) as u64)
    }

    fn read_value(&self, index: usize) -> T {
        let mut p = self.index_to_entry_addr(index);
        // ret = read_struct(ptr, &self.memory);
        let mut buf = if T::FIXED_SIZE {
            vec![0; T::MAX_SIZE as usize]
        } else {
            let size = read_u32(&self.memory, p) as usize;
            p += Bytes::from(4u64);
            vec![0; size]
        };
        self.memory.read(p.get(), &mut buf);
        T::from_bytes(buf)
    }

    fn write_value(&mut self, index: usize, value: &T) {
        let value = value.to_bytes();
        let mut p = self.index_to_entry_addr(index);
        if !T::FIXED_SIZE {
            write_u32(&self.memory, p, value.len() as u32);
            p += Bytes::from(4u64);
        }
        self.memory.write(p.get(), &value);
    }

    #[inline]
    pub fn push(&mut self, value: &T) {
        self.write_value(self.len(), value);
        self.len += 1;
        self.save();
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            self.save();
            Some(self.read_value(self.len()))
        }
    }

    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    pub unsafe fn get_unchecked(&self, index: usize) -> T {
        self.read_value(index)
    }

    pub fn get(&self, index: usize) -> Option<T> {
        if index >= self.len() {
            None
        } else {
            Some(self.read_value(index))
        }
    }

    pub fn set(&mut self, index: usize, value: &T) {
        assert!(index < self.len());
        self.write_value(index, value);
    }

    pub fn reserve(&mut self, additional: usize) {
        let page_size = WASM_PAGE_SIZE;
        let round_up = |x| ((x + page_size - 1) & !(page_size - 1));

        // We need to reserve space for the u32 that indicates the size.
        let add_bytes = (additional * Self::ENTRY_SIZE) as u64;
        let add_pages = round_up(add_bytes) / page_size;

        self.memory.grow(add_pages);
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        let page_size = WASM_PAGE_SIZE;
        let bytes = self.memory.size() * page_size;
        let free_bytes = bytes - StableVecHeader::size().get();
        (free_bytes / Self::ENTRY_SIZE as u64) as usize
    }
}

impl<M, T> Vec<M, T> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<M: Memory, T: BoundedStorable> From<(M, &[T])> for Vec<M, T> {
    fn from(s: (M, &[T])) -> Self {
        let mut v: Vec<M, T> = Vec::new(s.0);
        for t in s.1 {
            v.push(t);
        }
        v
    }
}

impl<M: Memory, T: BoundedStorable, const N: usize> From<(M, [T; N])> for Vec<M, T> {
    fn from(s: (M, [T; N])) -> Self {
        let slice: &[T] = &s.1;
        Vec::from((s.0, slice))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<std::vec::Vec<u8>>> {
        Rc::new(RefCell::new(std::vec::Vec::new()))
    }

    #[test]
    pub fn test_push_pop() {
        let mem = make_memory();
        let mut v = Vec::new(mem);
        v.push(&0u32);
        v.push(&1u32);

        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), Some(0));
        assert_eq!(v.pop(), None);
        assert_eq!(v.len(), 0);
    }

    #[test]
    pub fn test_clear() {
        let mem = make_memory();
        let mut v = Vec::from((mem, [0u32, 1u32]));

        v.clear();

        let val = 42;
        assert_eq!(v.pop(), None);
        v.push(&val);
        assert_eq!(v.pop(), Some(val));
    }

    #[test]
    pub fn test_load_from_mem() {
        let mem = make_memory();
        {
            let _v = Vec::from((mem.clone(), [0u32, 1u32, 2u32, 3u32, 4u32]));
        }

        let mut v: Vec<Rc<RefCell<std::vec::Vec<u8>>>, u32> = Vec::load(mem);

        assert_eq!(v.pop(), Some(4u32));
        assert_eq!(v.pop(), Some(3u32));
        assert_eq!(v.pop(), Some(2u32));
        assert_eq!(v.pop(), Some(1u32));
        assert_eq!(v.pop(), Some(0u32));

        assert_eq!(v.pop(), None);
    }
}
