use std::cell::OnceCell;

/// Estimates the in-process memory footprint of a value in bytes,
/// covering both inline (stack) and heap-allocated data.
///
/// Reports the logical data size, not the physical layout. Alignment
/// padding and allocator overhead are intentionally excluded — the
/// goal is to measure how much memory the data itself occupies.
///
/// ## Performance
///
/// Primitives, strings, and fixed-size containers are always O(1).
///
/// Vectors of types with a known `ELEMENT_SIZE` are also O(1),
/// using simple multiplication instead of traversal.
///
/// Types with a variable or unknown element size fall back to
/// per-element iteration, which is O(n). Implement `ELEMENT_SIZE`
/// for your fixed-size types to stay on the fast path.
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
        // size_of::<Option<T>>() already includes inline space for T.
        // Only add the heap portion of the inner value when populated.
        std::mem::size_of::<Self>()
            + self
                .as_ref()
                .map_or(0, |x| x.mem_size() - std::mem::size_of::<T>())
    }
}

impl<T: MemSize> MemSize for OnceCell<T> {
    #[inline]
    fn mem_size(&self) -> usize {
        // size_of::<OnceCell<T>>() already includes inline space for T.
        // Only add the heap portion of the inner value when populated.
        std::mem::size_of::<Self>()
            + self
                .get()
                .map_or(0, |x| x.mem_size() - std::mem::size_of::<T>())
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
        // Option<u64> stores u64 inline — no heap allocation.
        // size_of::<Option<u64>>() already includes space for the u64.
        let base = std::mem::size_of::<Option<u64>>();
        assert_eq!(None::<u64>.mem_size(), base);
        // Some(u64) has no heap data, so same as None.
        assert_eq!(Some(42u64).mem_size(), base);

        // Option<String> stores String inline — heap portion is the content.
        let base = std::mem::size_of::<Option<String>>();
        assert_eq!(None::<String>.mem_size(), base);
        // Some(String) adds only the heap-allocated content bytes.
        assert_eq!(Some(String::from("12345")).mem_size(), base + 5);
    }

    #[test]
    fn test_mem_size_once_cell() {
        // Empty cell: just the OnceCell wrapper (includes inline space for T).
        let base = std::mem::size_of::<OnceCell<Vec<u8>>>();
        let cell = OnceCell::<Vec<u8>>::new();
        assert_eq!(cell.mem_size(), base);

        // Populated with a Vec<u8> of 100 bytes:
        // OnceCell wrapper already includes the Vec header inline.
        // Only the heap-allocated element bytes (100) are added.
        let cell = OnceCell::from(vec![0u8; 100]);
        assert_eq!(cell.mem_size(), base + 100);
    }

    #[test]
    fn test_mem_size_tuple() {
        // Measures logical data size, not physical layout.
        // (u32, u64) = 4 + 8 = 12 bytes (padding excluded).
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
