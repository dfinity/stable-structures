use ic_stable_structures::storable::{Blob, Bound, Storable};
use std::borrow::Cow;
use tiny_rng::{Rand, Rng};

pub trait Random {
    fn random(rng: &mut Rng) -> Self;
}

impl<const K: usize> Random for Blob<K> {
    fn random(rng: &mut Rng) -> Self {
        let size = rng.rand_u32() % Blob::<K>::BOUND.max_size();
        Blob::try_from(
            rng.iter(Rand::rand_u8)
                .take(size as usize)
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .unwrap()
    }
}

impl<const K: usize> Random for UnboundedVecN<K> {
    fn random(rng: &mut Rng) -> Self {
        let size = rng.rand_u32() % Self::max_size();
        let mut buf = Vec::with_capacity(size as usize);
        for _ in 0..size {
            buf.push(rng.rand_u8());
        }
        Self::from(&buf)
    }
}

impl<const K: usize> Random for BoundedVecN<K> {
    fn random(rng: &mut Rng) -> Self {
        let size = rng.rand_u32() % Self::max_size();
        let mut buf = Vec::with_capacity(size as usize);
        for _ in 0..size {
            buf.push(rng.rand_u8());
        }
        Self::from(&buf)
    }
}

impl Random for u64 {
    fn random(rng: &mut Rng) -> Self {
        rng.rand_u64()
    }
}

/// Unbounded vector of bytes, always of length `N`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct UnboundedVecN<const N: usize>(Vec<u8>);

impl<const N: usize> UnboundedVecN<N> {
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

impl<const N: usize> Default for UnboundedVecN<N> {
    fn default() -> Self {
        Self(vec![0; N])
    }
}

impl<const N: usize> Storable for UnboundedVecN<N> {
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.0.clone())
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
    fn to_bytes(&self) -> Cow<[u8]> {
        Cow::Owned(self.0.clone())
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
