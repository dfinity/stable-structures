use ic_stable_structures::storable::{Blob, BoundedVecN, Storable, UnboundedVecN};
use std::convert::{From, TryFrom};
use tiny_rng::{Rand, Rng};

pub trait Random {
    fn random(rng: &mut Rng) -> Self;
}

#[inline]
fn random_bytes(rng: &mut Rng, max_size: u32) -> Vec<u8> {
    let size = (rng.rand_u32() % (max_size + 1)) as usize;
    if size == 0 {
        Vec::new()
    } else {
        let mut buf = Vec::with_capacity(size);
        buf.extend(rng.iter(Rand::rand_u8).take(size));
        buf
    }
}

impl<const K: usize> Random for Blob<K> {
    #[inline]
    fn random(rng: &mut Rng) -> Self {
        let bytes = random_bytes(rng, Blob::<K>::BOUND.max_size());
        Blob::try_from(&bytes[..]).unwrap()
    }
}

impl<const K: usize> Random for UnboundedVecN<K> {
    #[inline]
    fn random(rng: &mut Rng) -> Self {
        let bytes = random_bytes(rng, Self::max_size());
        Self::from(bytes)
    }
}

impl<const K: usize> Random for BoundedVecN<K> {
    #[inline]
    fn random(rng: &mut Rng) -> Self {
        let bytes = random_bytes(rng, Self::max_size());
        Self::from(bytes)
    }
}

impl Random for u64 {
    #[inline]
    fn random(rng: &mut Rng) -> Self {
        rng.rand_u64()
    }
}
