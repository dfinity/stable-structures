use std::cell::OnceCell;

/// Trait to estimate the total memory footprint of a value in bytes,
/// including both stack and heap usage.
///
/// For primitives, this returns the stack size.
/// For containers like `Vec` or `String`, this returns the stack size
/// (pointer + length + capacity) plus the size of the heap-allocated contents.
/// For borrowed types like `&str` and `[u8]`, this returns only the content
/// size, since the container overhead is accounted for by the owner.
pub trait MemSize {
    /// The fixed size of a single element, if known at compile time.
    /// Used by `Vec<T>` to compute `len * ELEMENT_SIZE` instead of iterating.
    /// Types with heap allocations or variable size should leave this as `None`.
    const ELEMENT_SIZE: Option<usize> = None;

    /// Returns the estimated total memory footprint of this value in bytes.
    fn mem_size(&self) -> usize;
}

impl MemSize for () {
    const ELEMENT_SIZE: Option<usize> = Some(0);

    #[inline]
    fn mem_size(&self) -> usize {
        0
    }
}

impl MemSize for u8 {
    const ELEMENT_SIZE: Option<usize> = Some(std::mem::size_of::<u8>());

    #[inline]
    fn mem_size(&self) -> usize {
        std::mem::size_of::<u8>()
    }
}

impl MemSize for [u8] {
    #[inline]
    fn mem_size(&self) -> usize {
        std::mem::size_of_val(self)
    }
}

impl MemSize for u32 {
    const ELEMENT_SIZE: Option<usize> = Some(std::mem::size_of::<u32>());

    #[inline]
    fn mem_size(&self) -> usize {
        std::mem::size_of::<u32>()
    }
}

impl MemSize for u64 {
    const ELEMENT_SIZE: Option<usize> = Some(std::mem::size_of::<u64>());

    #[inline]
    fn mem_size(&self) -> usize {
        std::mem::size_of::<u64>()
    }
}

impl MemSize for &str {
    #[inline]
    fn mem_size(&self) -> usize {
        self.as_bytes().mem_size()
    }
}

impl MemSize for String {
    #[inline]
    fn mem_size(&self) -> usize {
        std::mem::size_of::<Self>() + self.as_bytes().mem_size()
    }
}

impl<T: MemSize> MemSize for Vec<T> {
    #[inline]
    fn mem_size(&self) -> usize {
        let elements_size = match T::ELEMENT_SIZE {
            Some(el_size) => self.len() * el_size,
            None => self.iter().map(|x| x.mem_size()).sum::<usize>(),
        };
        std::mem::size_of::<Self>() + elements_size
    }
}

impl<T: MemSize> MemSize for Option<T> {
    #[inline]
    fn mem_size(&self) -> usize {
        std::mem::size_of::<Self>() + self.as_ref().map_or(0, |x| x.mem_size())
    }
}

impl<T: MemSize> MemSize for OnceCell<T> {
    #[inline]
    fn mem_size(&self) -> usize {
        std::mem::size_of::<Self>() + self.get().map_or(0, |x| x.mem_size())
    }
}

impl<A: MemSize, B: MemSize> MemSize for (A, B) {
    #[inline]
    fn mem_size(&self) -> usize {
        self.0.mem_size() + self.1.mem_size()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mem_size_u8() {
        assert_eq!(0_u8.mem_size(), 1);
        assert_eq!(42_u8.mem_size(), 1);
    }

    #[test]
    fn test_mem_size_u8_slice() {
        let a: [u8; 0] = [];
        assert_eq!(a.mem_size(), 0);
        assert_eq!([1_u8].mem_size(), 1);
        assert_eq!([1_u8, 2_u8].mem_size(), 2);
    }

    #[test]
    fn test_mem_size_u32() {
        assert_eq!(0_u32.mem_size(), 4);
        assert_eq!(42_u32.mem_size(), 4);
    }

    #[test]
    fn test_mem_size_u64() {
        assert_eq!(0_u64.mem_size(), 8);
        assert_eq!(42_u64.mem_size(), 8);
    }

    #[test]
    fn test_mem_size_u8_vec() {
        let base = std::mem::size_of::<Vec<u8>>();
        assert_eq!(Vec::<u8>::from([]).mem_size(), base);
        assert_eq!(Vec::<u8>::from([1]).mem_size(), base + 1);
        assert_eq!(Vec::<u8>::from([1, 2]).mem_size(), base + 2);
    }

    #[test]
    fn test_mem_size_str() {
        assert_eq!("a".mem_size(), 1);
        assert_eq!("ab".mem_size(), 2);
    }

    #[test]
    fn test_mem_size_string() {
        let base = std::mem::size_of::<String>();
        assert_eq!(String::from("a").mem_size(), base + 1);
        assert_eq!(String::from("ab").mem_size(), base + 2);
        for size_bytes in 0..1_024 {
            assert_eq!(
                String::from_utf8(vec![b'x'; size_bytes])
                    .unwrap()
                    .mem_size(),
                base + size_bytes
            );
        }
    }
}
