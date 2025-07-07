use ic_stable_structures::storable::{Bound, Storable};
use std::borrow::Cow;

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
    pub fn max_size() -> u32 {
        N as u32
    }

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
