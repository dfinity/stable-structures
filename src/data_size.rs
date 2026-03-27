/// Trait to estimate the total memory footprint of a value in bytes,
/// including both stack and heap usage.
///
/// For primitives, this returns the stack size.
/// For containers like `Vec` or `String`, this returns the stack size
/// (pointer + length + capacity) plus the size of the heap-allocated contents.
/// For borrowed types like `&str` and `[u8]`, this returns only the content
/// size, since the container overhead is accounted for by the owner.
pub trait DataSize {
    /// Returns the estimated total memory footprint of this value in bytes.
    fn data_size(&self) -> usize;
}

impl DataSize for u8 {
    fn data_size(&self) -> usize {
        std::mem::size_of::<u8>()
    }
}

impl DataSize for [u8] {
    fn data_size(&self) -> usize {
        std::mem::size_of_val(self)
    }
}

impl DataSize for u64 {
    fn data_size(&self) -> usize {
        std::mem::size_of::<u64>()
    }
}

impl DataSize for &str {
    fn data_size(&self) -> usize {
        self.as_bytes().data_size()
    }
}

impl DataSize for String {
    fn data_size(&self) -> usize {
        std::mem::size_of::<Self>() + self.as_bytes().data_size()
    }
}

impl<T: DataSize> DataSize for Vec<T> {
    fn data_size(&self) -> usize {
        std::mem::size_of::<Self>() + self.iter().map(|x| x.data_size()).sum::<usize>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_size_u8() {
        assert_eq!(0_u8.data_size(), 1);
        assert_eq!(42_u8.data_size(), 1);
    }

    #[test]
    fn test_data_size_u8_slice() {
        let a: [u8; 0] = [];
        assert_eq!(a.data_size(), 0);
        assert_eq!([1_u8].data_size(), 1);
        assert_eq!([1_u8, 2_u8].data_size(), 2);
    }

    #[test]
    fn test_data_size_u64() {
        assert_eq!(0_u64.data_size(), 8);
        assert_eq!(42_u64.data_size(), 8);
    }

    #[test]
    fn test_data_size_u8_vec() {
        let base = std::mem::size_of::<Vec<u8>>();
        assert_eq!(Vec::<u8>::from([]).data_size(), base);
        assert_eq!(Vec::<u8>::from([1]).data_size(), base + 1);
        assert_eq!(Vec::<u8>::from([1, 2]).data_size(), base + 2);
    }

    #[test]
    fn test_data_size_str() {
        assert_eq!("a".data_size(), 1);
        assert_eq!("ab".data_size(), 2);
    }

    #[test]
    fn test_data_size_string() {
        let base = std::mem::size_of::<String>();
        assert_eq!(String::from("a").data_size(), base + 1);
        assert_eq!(String::from("ab").data_size(), base + 2);
        for size_bytes in 0..1_024 {
            assert_eq!(
                String::from_utf8(vec![b'x'; size_bytes])
                    .unwrap()
                    .data_size(),
                base + size_bytes
            );
        }
    }
}
