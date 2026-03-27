use std::cell::OnceCell;

/// Estimates the in-process memory footprint of a value in bytes.
///
/// - Primitives return `size_of::<Self>()`. Always O(1).
/// - Containers (`Vec`, `String`) return their inline size plus
///   the size of the heap-allocated buffer. `Vec<T>` is O(1) when
///   `T::ELEMENT_SIZE` is `Some` (uses `len * element_size`), but
///   O(n) when `ELEMENT_SIZE` is `None` (falls back to per-element
///   iteration). Set `ELEMENT_SIZE` for fixed-size types to avoid this.
/// - Wrappers (`Option`, `OnceCell`) return their inline size plus
///   the inner value's `mem_size()` when populated. O(1) if the
///   inner type is O(1).
pub trait MemSize {
    /// Fixed per-element size, if known at compile time.
    /// When `Some`, `Vec<T>::mem_size()` uses `len * ELEMENT_SIZE` (O(1))
    /// instead of iterating (O(n)). Defaults to `None`.
    const ELEMENT_SIZE: Option<usize> = None;

    /// Returns the estimated memory footprint of this value in bytes.
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

    #[test]
    fn test_mem_size_unit() {
        assert_eq!(().mem_size(), 0);
        assert_eq!(<() as MemSize>::ELEMENT_SIZE, Some(0));
    }

    #[test]
    fn test_mem_size_vec_with_element_size() {
        // Vec<u32> uses the ELEMENT_SIZE fast path (Some(4)).
        let base = std::mem::size_of::<Vec<u32>>();
        assert_eq!(Vec::<u32>::new().mem_size(), base);
        assert_eq!(vec![1u32].mem_size(), base + 4);
        assert_eq!(vec![1u32, 2, 3].mem_size(), base + 12);
    }

    #[test]
    fn test_mem_size_vec_without_element_size() {
        // Vec<String> has ELEMENT_SIZE = None, falls back to iteration.
        let base = std::mem::size_of::<Vec<String>>();
        let string_base = std::mem::size_of::<String>();
        assert_eq!(Vec::<String>::new().mem_size(), base);
        // Each String reports size_of::<String>() + content_len.
        assert_eq!(vec![String::from("ab")].mem_size(), base + string_base + 2);
        assert_eq!(
            vec![String::from("a"), String::from("bc")].mem_size(),
            base + 2 * string_base + 3
        );
    }

    #[test]
    fn test_mem_size_option() {
        let base = std::mem::size_of::<Option<u64>>();
        // None: just the Option wrapper.
        assert_eq!(None::<u64>.mem_size(), base);
        // Some: wrapper + inner value.
        assert_eq!(Some(42u64).mem_size(), base + 8);
    }

    #[test]
    fn test_mem_size_once_cell() {
        // Empty cell: just the OnceCell wrapper.
        let base = std::mem::size_of::<OnceCell<Vec<u8>>>();
        let cell = OnceCell::<Vec<u8>>::new();
        assert_eq!(cell.mem_size(), base);

        // Populated with a Vec<u8> of 100 bytes:
        // OnceCell wrapper + Vec header (24) + 100 element bytes.
        let vec_base = std::mem::size_of::<Vec<u8>>();
        let cell = OnceCell::from(vec![0u8; 100]);
        assert_eq!(cell.mem_size(), base + vec_base + 100);
    }

    #[test]
    fn test_mem_size_tuple() {
        // (u32, u64) = 4 + 8 = 12 bytes.
        assert_eq!((1u32, 2u64).mem_size(), 4 + 8);
        // ((), u8) = 0 + 1 = 1 byte.
        assert_eq!(((), 0u8).mem_size(), 1);
    }

    #[test]
    fn test_element_size_constants() {
        assert_eq!(<u8 as MemSize>::ELEMENT_SIZE, Some(1));
        assert_eq!(<u32 as MemSize>::ELEMENT_SIZE, Some(4));
        assert_eq!(<u64 as MemSize>::ELEMENT_SIZE, Some(8));
        // String has no fixed element size.
        assert_eq!(<String as MemSize>::ELEMENT_SIZE, None);
    }
}
