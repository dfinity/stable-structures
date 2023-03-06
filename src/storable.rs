use std::borrow::{Borrow, Cow};
use std::cmp::Ordering;
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
}

/// A trait indicating that a `Storable` element is bounded in size.
pub trait BoundedStorable: Storable {
    /// The maximum size, in bytes, of the type when serialized.
    const MAX_SIZE: u32;

    /// True if all the values of this type have fixed-width encoding.
    /// Some data structures, such as stable vector, can take
    /// advantage of fixed size to avoid storing an explicit entry
    /// size.
    ///
    /// Examples: little-/big-endian encoding of u16/u32/u64, tuples
    /// and arrays of fixed-size types.
    const IS_FIXED_SIZE: bool;
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

impl<const N: usize> BoundedStorable for Blob<N> {
    const MAX_SIZE: u32 = N as u32;
    const IS_FIXED_SIZE: bool = false;
}

impl<const N: usize> Storable for Blob<N> {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(self.as_slice())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::try_from(bytes.borrow()).unwrap()
    }
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
}

impl BoundedStorable for () {
    const MAX_SIZE: u32 = 0;
    const IS_FIXED_SIZE: bool = false;
}

impl Storable for Vec<u8> {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(self)
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        bytes.to_vec()
    }
}

impl Storable for String {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Borrowed(self.as_bytes())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        String::from_utf8(bytes.to_vec()).unwrap()
    }
}

impl Storable for u128 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }
}

impl BoundedStorable for u128 {
    const MAX_SIZE: u32 = 16;
    const IS_FIXED_SIZE: bool = true;
}

impl Storable for u64 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }
}

impl BoundedStorable for u64 {
    const MAX_SIZE: u32 = 8;
    const IS_FIXED_SIZE: bool = true;
}

impl Storable for f64 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }
}

impl BoundedStorable for f64 {
    const MAX_SIZE: u32 = 8;
    const IS_FIXED_SIZE: bool = true;
}

impl Storable for u32 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }
}

impl BoundedStorable for u32 {
    const MAX_SIZE: u32 = 4;
    const IS_FIXED_SIZE: bool = true;
}

impl Storable for f32 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }
}

impl BoundedStorable for f32 {
    const MAX_SIZE: u32 = 4;
    const IS_FIXED_SIZE: bool = true;
}

impl Storable for u16 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }
}

impl BoundedStorable for u16 {
    const MAX_SIZE: u32 = 2;
    const IS_FIXED_SIZE: bool = true;
}

impl Storable for u8 {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.to_be_bytes().to_vec())
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        Self::from_be_bytes(bytes.as_ref().try_into().unwrap())
    }
}

impl BoundedStorable for u8 {
    const MAX_SIZE: u32 = 1;
    const IS_FIXED_SIZE: bool = true;
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
}

impl<const N: usize> BoundedStorable for [u8; N] {
    const MAX_SIZE: u32 = N as u32;
    const IS_FIXED_SIZE: bool = true;
}

impl<A, B> Storable for (A, B)
where
    A: BoundedStorable + Default,
    B: BoundedStorable + Default,
{
    fn to_bytes(&self) -> Cow<[u8]> {
        let mut bytes = vec![0; Self::MAX_SIZE as usize];
        let a_bytes = self.0.to_bytes();
        let b_bytes = self.1.to_bytes();

        let a_max_size = max_size(&self.0);
        let b_max_size = max_size(&self.1);

        debug_assert!(a_bytes.len() <= a_max_size);
        debug_assert!(b_bytes.len() <= b_max_size);

        bytes[0..a_bytes.len()].copy_from_slice(a_bytes.borrow());
        bytes[a_max_size..a_max_size + b_bytes.len()].copy_from_slice(b_bytes.borrow());

        let a_size_len = bytes_to_store_size::<A>() as usize;
        let b_size_len = bytes_to_store_size::<B>() as usize;

        let sizes_offset: usize = a_max_size + b_max_size;

        encode_size::<A>(
            &mut bytes[sizes_offset..sizes_offset + a_size_len],
            a_bytes.len(),
        );
        encode_size::<B>(
            &mut bytes[sizes_offset + a_size_len..sizes_offset + a_size_len + b_size_len],
            b_bytes.len(),
        );

        Cow::Owned(bytes)
    }

    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        assert_eq!(bytes.len(), Self::MAX_SIZE as usize);

        // Rust doesn't allow us to access A::MAX_SIZE here but type
        // deduction from values seems to do the trick. Hence the
        // Default bound on the Storable impl.
        let (a, b) = Self::default();
        let a_max_size = max_size(&a);
        let b_max_size = max_size(&b);
        let sizes_offset = a_max_size + b_max_size;

        let a_size_len = bytes_to_store_size::<A>() as usize;
        let b_size_len = bytes_to_store_size::<B>() as usize;
        let a_len = decode_size::<A>(&bytes[sizes_offset..sizes_offset + a_size_len]);
        let b_len = decode_size::<B>(
            &bytes[sizes_offset + a_size_len..sizes_offset + a_size_len + b_size_len],
        );

        let a = A::from_bytes(Cow::Borrowed(&bytes[0..a_len]));
        let b = B::from_bytes(Cow::Borrowed(&bytes[a_max_size..a_max_size + b_len]));

        (a, b)
    }
}

impl<A, B> BoundedStorable for (A, B)
where
    A: BoundedStorable + Default,
    B: BoundedStorable + Default,
{
    const MAX_SIZE: u32 =
        A::MAX_SIZE + B::MAX_SIZE + bytes_to_store_size::<A>() + bytes_to_store_size::<B>();
    const IS_FIXED_SIZE: bool = A::IS_FIXED_SIZE && B::IS_FIXED_SIZE;
}

const fn max_size<A: BoundedStorable>(_: &A) -> usize {
    A::MAX_SIZE as usize
}

fn decode_size<A: BoundedStorable>(src: &[u8]) -> usize {
    if A::IS_FIXED_SIZE {
        A::MAX_SIZE as usize
    } else if A::MAX_SIZE <= u8::MAX as u32 {
        src[0] as usize
    } else if A::MAX_SIZE <= u16::MAX as u32 {
        u16::from_be_bytes([src[0], src[1]]) as usize
    } else {
        u32::from_be_bytes([src[0], src[1], src[2], src[3]]) as usize
    }
}

fn encode_size<A: BoundedStorable>(dst: &mut [u8], n: usize) {
    if A::IS_FIXED_SIZE {
        return;
    }

    if A::MAX_SIZE <= u8::MAX as u32 {
        dst[0] = n as u8;
    } else if A::MAX_SIZE <= u16::MAX as u32 {
        dst[0..2].copy_from_slice(&(n as u16).to_be_bytes());
    } else {
        dst[0..4].copy_from_slice(&(n as u32).to_be_bytes());
    }
}

pub(crate) const fn bytes_to_store_size<A: BoundedStorable>() -> u32 {
    if A::IS_FIXED_SIZE {
        0
    } else if A::MAX_SIZE <= u8::MAX as u32 {
        1
    } else if A::MAX_SIZE <= u16::MAX as u32 {
        2
    } else {
        4
    }
}
