use ic_principal::Principal;
use std::borrow::{Borrow, Cow};
use std::cmp::{Ordering, Reverse};
use std::convert::{TryFrom, TryInto};
use std::fmt;

mod tuples;

#[cfg(test)]
mod tests;

/// A trait with convenience methods for storing an element into a stable structure.
pub trait Storable {
    /// Converts the element into a possibly borrowed byte slice.
    ///
    /// NOTE: `Cow` is used here to avoid unnecessary cloning.
    fn to_bytes(&self) -> Cow<'_, [u8]>;

    /// Converts the element into an owned byte vector.
    ///
    /// This method consumes `self` and avoids cloning when possible.
    fn into_bytes(self) -> Vec<u8>;

    /// Converts bytes into an element.
    fn from_bytes(bytes: Cow<[u8]>) -> Self;

    /// The size bounds of the type.
    const BOUND: Bound;

    /// Like `to_bytes`, but checks that bytes conform to declared bounds.
    fn to_bytes_checked(&self) -> Cow<'_, [u8]> {
        let bytes = self.to_bytes();
        Self::check_bounds(&bytes);
        bytes
    }

    /// Like `into_bytes`, but checks that bytes conform to declared bounds.
    fn into_bytes_checked(self) -> Vec<u8>
    where
        Self: Sized,
    {
        let bytes = self.into_bytes();
        Self::check_bounds(&bytes);
        bytes
    }

    /// Validates that a byte slice fits within this type's declared bounds.
    #[inline]
    fn check_bounds(bytes: &[u8]) {
        if let Bound::Bounded {
            max_size,
            is_fixed_size,
        } = Self::BOUND
        {
            let actual = bytes.len();
            if is_fixed_size {
                assert_eq!(
                    actual, max_size as usize,
                    "expected a fixed-size element with length {} bytes, but found {} bytes",
                    max_size, actual
                );
            } else {
                assert!(
                    actual <= max_size as usize,
                    "expected an element with length <= {} bytes, but found {} bytes",
                    max_size,
                    actual
                );
            }
        }
    }
}

#[derive(Debug, PartialEq)]
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
        Some(self.cmp(other))
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
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self.as_slice())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.as_slice().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::try_from(bytes.borrow()).unwrap()
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: N as u32,
        is_fixed_size: false,
    };
}

/// Unbounded vector of bytes, always of length `N`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct UnboundedVecN<const N: usize>(Vec<u8>);

impl<const N: usize> UnboundedVecN<N> {
    pub const MAX_SIZE: u32 = N as u32;

    pub fn from(slice: &[u8]) -> Self {
        assert!(
            slice.len() <= N,
            "expected a slice with length <= {} bytes, but found {} bytes",
            N,
            slice.len()
        );
        let mut vec = Vec::with_capacity(N);
        vec.extend_from_slice(slice);
        vec.resize(N, 0);
        Self(vec)
    }
}

impl<const N: usize> Default for UnboundedVecN<N> {
    fn default() -> Self {
        Self(vec![0; N])
    }
}

impl<const N: usize> Storable for UnboundedVecN<N> {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.0.clone())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.0
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self(bytes.into_owned())
    }

    const BOUND: Bound = Bound::Unbounded;
}

/// Bounded vector of bytes, always of length `N`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct BoundedVecN<const N: usize>(Vec<u8>);

impl<const N: usize> BoundedVecN<N> {
    pub const MAX_SIZE: u32 = N as u32;

    pub fn from(slice: &[u8]) -> Self {
        assert!(
            slice.len() <= N,
            "expected a slice with length <= {} bytes, but found {} bytes",
            N,
            slice.len()
        );
        let mut vec = Vec::with_capacity(N);
        vec.extend_from_slice(slice);
        vec.resize(N, 0);
        Self(vec)
    }
}

impl<const N: usize> Default for BoundedVecN<N> {
    fn default() -> Self {
        Self(vec![0; N])
    }
}

impl<const N: usize> Storable for BoundedVecN<N> {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.0.clone())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.0
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self(bytes.into_owned())
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
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(&[])
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        Vec::new()
    }

    #[inline]
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
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self)
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        bytes.into_owned()
    }

    const BOUND: Bound = Bound::Unbounded;
}

impl Storable for String {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self.as_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.into_bytes()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        String::from_utf8(bytes.into_owned()).unwrap()
    }

    const BOUND: Bound = Bound::Unbounded;
}

impl Storable for u128 {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.into_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 16,
        is_fixed_size: true,
    };
}

impl Storable for u64 {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.into_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 8,
        is_fixed_size: true,
    };
}

impl Storable for f64 {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.into_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 8,
        is_fixed_size: true,
    };
}

impl Storable for u32 {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.into_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 4,
        is_fixed_size: true,
    };
}

impl Storable for f32 {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.into_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 4,
        is_fixed_size: true,
    };
}

impl Storable for u16 {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.into_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 2,
        is_fixed_size: true,
    };
}

impl Storable for u8 {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(self.into_bytes())
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 1,
        is_fixed_size: true,
    };
}

impl Storable for bool {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Owned(if *self { 1_u8 } else { 0_u8 }.to_be_bytes().to_vec())
    }

    fn into_bytes(self) -> Vec<u8> {
        if self { 1_u8 } else { 0_u8 }.to_be_bytes().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        assert_eq!(bytes.len(), 1);
        match bytes[0] {
            0 => false,
            1 => true,
            other => panic!("Invalid bool encoding: expected 0 or 1, found {}", other),
        }
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: 1,
        is_fixed_size: true,
    };
}

impl<const N: usize> Storable for [u8; N] {
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(&self[..])
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.to_vec()
    }

    #[inline]
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
    #[inline]
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        self.0.to_bytes()
    }

    #[inline]
    fn into_bytes(self) -> Vec<u8> {
        self.0.into_bytes()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self(T::from_bytes(bytes))
    }

    const BOUND: Bound = T::BOUND;
}

impl<T: Storable> Storable for Option<T> {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        match self {
            Some(t) => {
                let mut bytes = t.to_bytes().into_owned();
                bytes.push(1);
                Cow::Owned(bytes)
            }
            None => Cow::Borrowed(&[0]),
        }
    }

    fn into_bytes(self) -> Vec<u8> {
        match self {
            Some(t) => {
                let mut bytes = t.into_bytes();
                bytes.push(1);
                bytes
            }
            None => vec![0],
        }
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        match bytes.split_last() {
            Some((last, rest)) => match last {
                0 => {
                    assert!(rest.is_empty(), "Invalid Option encoding: unexpected prefix before the None marker: {rest:?}");
                    None
                }
                1 => Some(T::from_bytes(Cow::Borrowed(rest))),
                _ => panic!("Invalid Option encoding: unexpected variant marker {last}"),
            },
            None => panic!("Invalid Option encoding: expected at least one byte"),
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

impl Storable for Principal {
    fn to_bytes(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self.as_slice())
    }

    fn into_bytes(self) -> Vec<u8> {
        self.as_slice().to_vec()
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_slice(&bytes)
    }

    const BOUND: Bound = Bound::Bounded {
        max_size: Principal::MAX_LENGTH_IN_BYTES as u32,
        is_fixed_size: false,
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

pub(crate) const fn bytes_to_store_size_bounded(bounds: &Bounds) -> u32 {
    if bounds.is_fixed_size {
        0
    } else {
        bytes_to_store_size(bounds.max_size as usize) as u32
    }
}

const fn bytes_to_store_size(bytes_size: usize) -> usize {
    if bytes_size <= u8::MAX as usize {
        1
    } else if bytes_size <= u16::MAX as usize {
        2
    } else {
        4
    }
}
