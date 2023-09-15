use std::borrow::{Borrow, Cow};
use std::cmp::{Ordering, Reverse};
use std::convert::{TryFrom, TryInto};
use std::fmt;

#[cfg(test)]
mod tests;

/// A trait with convenience methods for storing an element into a stable structure.
pub trait Storable {
    /// Converts an element into bytes.
    ///
    /// NOTE: `Cow` is used here to avoid unnecessary cloning.
    fn to_bytes(&self) -> Cow<[u8]>;

    /// Converts bytes into an element.
    fn from_bytes(bytes: Cow<[u8]>) -> Self;

    /// The size bounds of the type.
    const BOUND: Bound;

    /// Like `to_bytes`, but includes additional checks to ensure the element's serialized bytes
    /// are within the element's bounds.
    fn to_bytes_checked(&self) -> Cow<[u8]> {
        let bytes = self.to_bytes();
        if let Bound::Bounded {
            max_size,
            is_fixed_size,
        } = Self::BOUND
        {
            if is_fixed_size {
                assert_eq!(
                    bytes.len(),
                    max_size as usize,
                    "expected a fixed-size element with length {} bytes, but found {} bytes",
                    max_size,
                    bytes.len()
                );
            } else {
                assert!(
                    bytes.len() <= max_size as usize,
                    "expected an element with length <= {} bytes, but found {} bytes",
                    max_size,
                    bytes.len()
                );
            }
        }
        bytes
    }
}

/// States whether the type's size is bounded or unbounded.
pub enum Bound {
    /// The type has no size bounds.
    Unbounded,

    /// The type has size bounds.
    Bounded {
        /// The maximum size, in bytes, of the type when serialized.
        max_size: u32,

        /// True if all the values of this type have fixed-width encoding.
        /// Some data structures, such as stable vector, can take
        /// advantage of fixed size to avoid storing an explicit entry
        /// size.
        ///
        /// Examples: little-/big-endian encoding of u16/u32/u64, tuples
        /// and arrays of fixed-size types.
        is_fixed_size: bool,
    },
}

impl Bound {
    /// Returns the maximum size of the type if bounded, panics if unbounded.
    pub const fn max_size(&self) -> u32 {
        if let Bound::Bounded { max_size, .. } = self {
            *max_size
        } else {
            panic!("Cannot get max size of unbounded type.");
        }
    }

    /// Returns true if the type is fixed in size, false otherwise.
    pub const fn is_fixed_size(&self) -> bool {
        if let Bound::Bounded { is_fixed_size, .. } = self {
            *is_fixed_size
        } else {
            false
        }
    }
}

/// Variable-size, but limited in capacity byte array.
#[derive(Eq, Copy, Clone)]
pub struct Blob<const N: usize> {
    storage: [u8; N],
    size: u32,
}

impl<const N: usize> Blob<N> {
    /// Returns the contents of this array as a byte slice.
    pub fn as_slice(&self) -> &[u8] {
        &self.storage[0..self.len()]
    }

    /// Returns true if the array is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the actual length of this array.
    pub fn len(&self) -> usize {
        self.size as usize
    }
}

impl<const N: usize> Default for Blob<N> {
    fn default() -> Self {
        Self {
            storage: [0; N],
            size: 0,
        }
    }
}

#[derive(Debug)]
pub struct TryFromSliceError;

impl<const N: usize> TryFrom<&[u8]> for Blob<N> {
    type Error = TryFromSliceError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        if value.len() > N {
            return Err(TryFromSliceError);
        }
        let mut result = Self::default();
        result.storage[0..value.len()].copy_from_slice(value);
        result.size = value.len() as u32;
        Ok(result)
    }
}

impl<const N: usize> AsRef<[u8]> for Blob<N> {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<const N: usize> PartialEq for Blob<N> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}

impl<const N: usize> PartialOrd for Blob<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<const N: usize> Ord for Blob<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<const N: usize> fmt::Debug for Blob<N> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(fmt)
    }
}

impl<const N: usize> Storable for Blob<N> {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(self.as_slice())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::try_from(bytes.borrow()).unwrap()
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: N as u32,
        is_fixed_size: false,
    };
}

// NOTE: Below are a few implementations of `Storable` for common types.
// Some of these implementations use `unwrap`, as opposed to returning a `Result`
// with a possible error. The reason behind this decision is that these
// `unwrap`s would be triggered in one of the following cases:
//
// 1) The implementation of `Storable` has a bug.
// 2) The data being stored in the stable structure is corrupt.
//
// Both of these errors are irrecoverable at runtime, and given the additional
// complexity of exposing these errors in the API of stable structures, an `unwrap`
// in case of a detected error is preferable and safer.

impl Storable for () {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(&[])
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        assert!(bytes.is_empty());
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 0,
        // A `()` should in theory be fixed in size, but this flag was initially
        // set incorrectly and it cannot be fixed to maintain backward-compatibility.
        is_fixed_size: false,
    };
}

impl Storable for Vec<u8> {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(self)
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        bytes.to_vec()
    }

    const BOUND: Bound = Bound::Unbounded;
}

impl Storable for String {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(self.as_bytes())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        String::from_utf8(bytes.to_vec()).unwrap()
    }

    const BOUND: Bound = Bound::Unbounded;
}

impl Storable for u128 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 16,
        is_fixed_size: true,
    };
}

impl Storable for u64 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 8,
        is_fixed_size: true,
    };
}

impl Storable for f64 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 8,
        is_fixed_size: true,
    };
}

impl Storable for u32 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 4,
        is_fixed_size: true,
    };
}

impl Storable for f32 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 4,
        is_fixed_size: true,
    };
}

impl Storable for u16 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 2,
        is_fixed_size: true,
    };
}

impl Storable for u8 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 1,
        is_fixed_size: true,
    };
}

impl<const N: usize> Storable for [u8; N] {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(&self[..])
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        assert_eq!(bytes.len(), N);
        let mut arr = [0; N];
        arr[0..N].copy_from_slice(&bytes);
        arr
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: N as u32,
        is_fixed_size: true,
    };
}

impl<T: Storable> Storable for Reverse<T> {
    fn to_bytes(&self) -> Cow<[u8]> {
        self.0.to_bytes()
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self(T::from_bytes(bytes))
    }

    const BOUND: Bound = T::BOUND;
}

impl<A, B> Storable for (A, B)
where
    A: Storable,
    B: Storable,
{
    fn to_bytes(&self) -> Cow<[u8]> {
        match Self::BOUND {
            Bound::Bounded { max_size, .. } => {
                let mut bytes = vec![0; max_size as usize];
                let a_bytes = self.0.to_bytes();
                let b_bytes = self.1.to_bytes();

                let a_bounds = bounds::<A>();
                let b_bounds = bounds::<B>();

                let a_max_size = a_bounds.max_size as usize;
                let b_max_size = b_bounds.max_size as usize;

                debug_assert!(a_bytes.len() <= a_max_size);
                debug_assert!(b_bytes.len() <= b_max_size);

                bytes[0..a_bytes.len()].copy_from_slice(a_bytes.borrow());
                bytes[a_max_size..a_max_size + b_bytes.len()].copy_from_slice(b_bytes.borrow());

                let a_size_len = bytes_to_store_size(&a_bounds) as usize;
                let b_size_len = bytes_to_store_size(&b_bounds) as usize;

                let sizes_offset: usize = a_max_size + b_max_size;

                encode_size(
                    &mut bytes[sizes_offset..sizes_offset + a_size_len],
                    a_bytes.len(),
                    &a_bounds,
                );
                encode_size(
                    &mut bytes[sizes_offset + a_size_len..sizes_offset + a_size_len + b_size_len],
                    b_bytes.len(),
                    &b_bounds,
                );

                Cow::Owned(bytes)
            }
            _ => todo!("Serializing tuples with unbounded types is not yet supported."),
        }
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        match Self::BOUND {
            Bound::Bounded { max_size, .. } => {
                assert_eq!(bytes.len(), max_size as usize);

                let a_bounds = bounds::<A>();
                let b_bounds = bounds::<B>();
                let a_max_size = a_bounds.max_size as usize;
                let b_max_size = b_bounds.max_size as usize;
                let sizes_offset = a_max_size + b_max_size;

                let a_size_len = bytes_to_store_size(&a_bounds) as usize;
                let b_size_len = bytes_to_store_size(&b_bounds) as usize;
                let a_len = decode_size(&bytes[sizes_offset..sizes_offset + a_size_len], &a_bounds);
                let b_len = decode_size(
                    &bytes[sizes_offset + a_size_len..sizes_offset + a_size_len + b_size_len],
                    &b_bounds,
                );

                let a = A::from_bytes(Cow::Borrowed(&bytes[0..a_len]));
                let b = B::from_bytes(Cow::Borrowed(&bytes[a_max_size..a_max_size + b_len]));

                (a, b)
            }
            _ => todo!("Deserializing tuples with unbounded types is not yet supported."),
        }
    }

    const BOUND: Bound = {
        match (A::BOUND, B::BOUND) {
            (Bound::Bounded { .. }, Bound::Bounded { .. }) => {
                let a_bounds = bounds::<A>();
                let b_bounds = bounds::<B>();

                let max_size = a_bounds.max_size
                    + b_bounds.max_size
                    + bytes_to_store_size(&a_bounds)
                    + bytes_to_store_size(&b_bounds);

                let is_fixed_size = a_bounds.is_fixed_size && b_bounds.is_fixed_size;

                Bound::Bounded {
                    max_size,
                    is_fixed_size,
                }
            }
            _ => Bound::Unbounded,
        }
    };
}

impl<T: Storable> Storable for Option<T> {
    fn to_bytes(&self) -> Cow<[u8]> {
        match self {
            Some(t) => {
                let mut bytes = t.to_bytes().into_owned();
                bytes.push(1);
                Cow::Owned(bytes)
            }
            None => Cow::Borrowed(&[0]),
        }
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        match bytes.len() {
            0 => None,
            1 => {
                assert_eq!(bytes[0], 0, "Invalid Option encoding");
                None
            }
            _ => {
                assert_eq!(bytes[bytes.len() - 1], 1, "Invalid Option encoding");
                Some(T::from_bytes(Cow::Borrowed(&bytes[0..bytes.len() - 1])))
            }
        }
    }

    const BOUND: Bound = {
        match T::BOUND {
            Bound::Bounded {
                max_size,
                is_fixed_size,
            } => Bound::Bounded {
                max_size: max_size + 1,
                is_fixed_size,
            },
            Bound::Unbounded => Bound::Unbounded,
        }
    };
}

pub(crate) struct Bounds {
    pub max_size: u32,
    pub is_fixed_size: bool,
}

/// Returns the bounds of the given type, panics if unbounded.
pub(crate) const fn bounds<A: Storable>() -> Bounds {
    if let Bound::Bounded {
        max_size,
        is_fixed_size,
    } = A::BOUND
    {
        Bounds {
            max_size,
            is_fixed_size,
        }
    } else {
        panic!("Cannot get bounds of unbounded type.");
    }
}

/// Returns the max size of the given type if bounded, panics if unbounded.
pub const fn max_size<A: Storable>() -> u32 {
    if let Bound::Bounded { max_size, .. } = A::BOUND {
        max_size
    } else {
        panic!("Cannot get max size of unbounded type.");
    }
}

/// Returns true if the type is fixed in size, false otherwise.
pub const fn is_fixed_size<A: Storable>() -> bool {
    if let Bound::Bounded { is_fixed_size, .. } = A::BOUND {
        is_fixed_size
    } else {
        // Unbounded types do not have a fixed size.
        false
    }
}

fn decode_size(src: &[u8], bounds: &Bounds) -> usize {
    if bounds.is_fixed_size {
        bounds.max_size as usize
    } else if bounds.max_size <= u8::MAX as u32 {
        src[0] as usize
    } else if bounds.max_size <= u16::MAX as u32 {
        u16::from_be_bytes([src[0], src[1]]) as usize
    } else {
        u32::from_be_bytes([src[0], src[1], src[2], src[3]]) as usize
    }
}

fn encode_size(dst: &mut [u8], n: usize, bounds: &Bounds) {
    if bounds.is_fixed_size {
        return;
    }

    if bounds.max_size <= u8::MAX as u32 {
        dst[0] = n as u8;
    } else if bounds.max_size <= u16::MAX as u32 {
        dst[0..2].copy_from_slice(&(n as u16).to_be_bytes());
    } else {
        dst[0..4].copy_from_slice(&(n as u32).to_be_bytes());
    }
}

pub(crate) const fn bytes_to_store_size(bounds: &Bounds) -> u32 {
    if bounds.is_fixed_size {
        0
    } else if bounds.max_size <= u8::MAX as u32 {
        1
    } else if bounds.max_size <= u16::MAX as u32 {
        2
    } else {
        4
    }
}
