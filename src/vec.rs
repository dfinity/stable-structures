use std::marker::PhantomData;

use crate::{
    copy, read_struct,
    types::{Address, Bytes},
    write_struct, BoundedStorable, Memory,
};

const LAYOUT_VERSION: u8 = 1;
const MAGIC: &[u8; 3] = b"VEC";

pub struct StableVec<M, T> {
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
    len: usize,
    // Additional space reserved to add new fields without breaking backward-compatibility.
    _buffer: [u8; 24],
}

impl StableVecHeader {
    fn size() -> Bytes {
        Bytes::from(core::mem::size_of::<Self>() as u64)
    }
}

impl<M: Memory + Clone, T: BoundedStorable> StableVec<M, T> {
    #[must_use]
    pub fn new(memory: M) -> Self {
        Self::new_with_sizes(memory, T::max_size() as u64)
    }

    pub fn new_with_sizes(memory: M, max_value_size: u64) -> Self {
        let heap = Self {
            memory,
            max_value_size,
            base: Address::from(0) + StableVecHeader::size(),
            len: 0,
            _phantom: PhantomData,
        };

        heap.save();
        heap
    }

    pub fn load(memory: M) -> Self {
        Self::load_with_sizes(memory, T::max_size() as u64)
    }

    pub fn load_with_sizes(memory: M, max_value_size: u64) -> Self {
        // Read the header from memory.
        let header: StableVecHeader = read_struct(Address::from(0), &memory);
        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        assert_eq!(header.version, LAYOUT_VERSION, "Unsupported version.");
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
            len: self.len,
            _buffer: [0; 24],
        };

        write_struct(&header, Address::from(0), &self.memory);
    }

    fn index_to_addr(&self, index: usize) -> Address {
        self.base + Bytes::from(self.max_value_size * (index as u64))
    }
}

impl<M: Memory + Clone, T: BoundedStorable> StableVec<M, T> {
    #[inline]
    pub fn capacity(&self) -> usize {
        let page_size = 64 * 1024;
        let bytes = self.memory.size() * page_size;
        let free_bytes = bytes - StableVecHeader::size().get();
        (free_bytes / self.max_value_size) as usize
    }

    pub fn reserve(&mut self, additional: usize) {
        let page_size = 64 * 1024;
        let round_up = |x| ((x + page_size - 1) & !(page_size - 1));

        let add_bytes = additional as u64 * self.max_value_size;
        let add_pages = round_up(add_bytes) / page_size;

        self.memory.grow(add_pages);
    }

    pub fn insert(&mut self, index: usize, element: &T) {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("insertion index (is {index}) should be <= len (is {len})");
        }

        let len = self.len();
        if index > len {
            assert_failed(index, len);
        }

        // space for the new element
        if len == self.capacity() {
            self.reserve(1);
        }

        let p = self.index_to_addr(index);
        let src = p;
        let dst = p + Bytes::from(self.max_value_size as u64);
        copy::<T, M>(&self.memory, src, dst, (len - index) as u64);
        write_struct(element, p, &self.memory);

        self.len += 1;
    }

    pub fn remove(&mut self, index: usize) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("removal index (is {index}) should be < len (is {len})");
        }

        let len = self.len();
        if index >= len {
            assert_failed(index, len);
        }

        let ret;
        {
            let ptr = self.index_to_addr(index);
            ret = read_struct(ptr, &self.memory);

            // Shift everything down to fill in that spot.
            copy::<T, M>(
                &self.memory,
                self.index_to_addr(index + 1),
                ptr,
                (len - index - 1) as u64,
            );
        }
        self.len -= 1;
        ret
    }

    #[inline]
    pub fn push(&mut self, value: &T) {
        let end = self.index_to_addr(self.len);
        write_struct(value, end, &self.memory);
        self.len += 1;
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(read_struct(self.index_to_addr(self.len()), &self.memory))
        }
    }

    pub fn clear(&mut self) {
        self.len = 0;
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, index: usize) -> T {
        assert!(index < self.len());
        read_struct(self.index_to_addr(index), &self.memory)
    }

    pub fn set(&self, index: usize, value: T) {
        assert!(index < self.len());
        write_struct(&value, self.index_to_addr(index), &self.memory);
    }
}

impl<M: Memory + Clone, T: Clone + BoundedStorable> From<(M, &[T])> for StableVec<M, T> {
    fn from(s: (M, &[T])) -> Self {
        let mut v: StableVec<M, T> = StableVec::new(s.0);
        for t in s.1 {
            v.push(t);
        }
        v
    }
}

impl<M: Memory + Clone, T: Clone + BoundedStorable, const N: usize> From<(M, [T; N])>
    for StableVec<M, T>
{
    fn from(s: (M, [T; N])) -> Self {
        let slice: &[T] = &s.1;
        StableVec::from((s.0, slice))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    pub fn test_insert() {
        let mem = make_memory();
        let mut v = StableVec::new(mem);
        v.insert(0, &0u32);
        v.insert(1, &1u32);

        assert_eq!(v.len(), 2);
        assert_eq!(v.get(1), 1);
        assert_eq!(v.get(0), 0);
    }

    #[test]
    pub fn test_remove() {
        let mem = make_memory();
        let mut v = StableVec::from((mem, [0u32, 1u32]));

        assert_eq!(v.len(), 2);
        assert_eq!(v.get(1), 1);
        assert_eq!(v.get(0), 0);

        assert_eq!(v.remove(0), 0);
        assert_eq!(v.len(), 1);

        assert_eq!(v.remove(0), 1);
        assert_eq!(v.len(), 0);
    }

    #[test]
    pub fn test_push_pop() {
        let mem = make_memory();
        let mut v = StableVec::new(mem);
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
        let mut v = StableVec::from((mem, [0u32, 1u32]));

        v.clear();

        let val = 42;
        assert_eq!(v.pop(), None);
        v.push(&val);
        assert_eq!(v.pop(), Some(val));
    }
}
