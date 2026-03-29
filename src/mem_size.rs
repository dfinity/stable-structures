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

impl<T: MemSize> MemSize for Vec<T> {
    #[inline]
    fn mem_size(&self) -> usize {
        let elements_size = match T::ELEMENT_SIZE {
            // For fixed-size elements, the allocator reserves capacity * element_size bytes.
            Some(el_size) => self.capacity() * el_size,
            // For variable-size elements, we can only measure initialized elements
            // plus the slack from capacity - len (using size_of::<T>() per slack slot).
            None => {
                self.iter().map(|x| x.mem_size()).sum::<usize>()
                    + (self.capacity() - self.len()) * std::mem::size_of::<T>()
            }
        };
        std::mem::size_of::<Self>() + elements_size
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
    fn test_mem_size_unit() {
        assert_eq!(().mem_size(), 0);
    }

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
    fn test_mem_size_vec_with_element_size() {
        // Vec<u32> uses the ELEMENT_SIZE fast path (Some(4)).
        let base = std::mem::size_of::<Vec<u32>>();
        assert_eq!(Vec::<u32>::new().mem_size(), base);
        assert_eq!(vec![1_u32].mem_size(), base + 4);
        assert_eq!(vec![1_u32, 2, 3].mem_size(), base + 12);
    }

    #[test]
    fn test_mem_size_vec_without_element_size() {
        type Blob = Vec<u8>;
        // Vec<Blob> has ELEMENT_SIZE = None, falls back to per-element iteration.
        let base = std::mem::size_of::<Vec<Blob>>();
        let blob_base = std::mem::size_of::<Blob>();
        assert_eq!(Vec::<Blob>::new().mem_size(), base);
        // Each Blob reports size_of::<Blob>() + content_len.
        assert_eq!(vec![Blob::from([1, 2])].mem_size(), base + blob_base + 2);
        assert_eq!(
            vec![Blob::from([1]), Blob::from([2, 3])].mem_size(),
            base + 2 * blob_base + 3
        );
    }

    #[test]
    fn test_mem_size_tuple() {
        // Measures logical data size, not physical layout.
        // (u32, u64) = 4 + 8 = 12 bytes (padding excluded).
        assert_eq!((1_u32, 2_u64).mem_size(), 4 + 8);
    }

    #[test]
    fn test_mem_size_vec_measures_capacity_fixed_size() {
        // Vec<u32> has ELEMENT_SIZE = Some(4), so capacity is measured directly.
        let base = std::mem::size_of::<Vec<u32>>();
        let mut v = Vec::<u32>::with_capacity(10);
        // Empty but capacity = 10 → 10 * 4 = 40 bytes of heap.
        assert_eq!(v.mem_size(), base + 10 * 4);

        v.push(1);
        v.push(2);
        // len = 2, capacity = 10 → still 10 * 4 = 40.
        assert_eq!(v.len(), 2);
        assert_eq!(v.capacity(), 10);
        assert_eq!(v.mem_size(), base + 10 * 4);
    }

    #[test]
    fn test_mem_size_vec_measures_capacity_variable_size() {
        // Vec<Vec<u8>> has ELEMENT_SIZE = None → per-element iteration + slack.
        type Blob = Vec<u8>;
        let base = std::mem::size_of::<Vec<Blob>>();
        let blob_base = std::mem::size_of::<Blob>();

        let mut v = Vec::<Blob>::with_capacity(5);
        // Empty, capacity = 5 → 5 slack slots × size_of::<Blob>().
        assert_eq!(v.mem_size(), base + 5 * blob_base);

        v.push(Blob::from([1, 2, 3]));
        // len = 1 (blob_base + 3), slack = 4 × blob_base.
        assert_eq!(v.len(), 1);
        assert_eq!(v.capacity(), 5);
        assert_eq!(v.mem_size(), base + (blob_base + 3) + 4 * blob_base);
    }

    #[test]
    fn test_element_size_constants() {
        assert_eq!(<u8 as MemSize>::ELEMENT_SIZE, Some(1));
        assert_eq!(<u32 as MemSize>::ELEMENT_SIZE, Some(4));
        assert_eq!(<u64 as MemSize>::ELEMENT_SIZE, Some(8));
        // Vec<u8> has no fixed element size.
        assert_eq!(<Vec<u8> as MemSize>::ELEMENT_SIZE, None);
    }
}
