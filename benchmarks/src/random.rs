use crate::vec::{BoundedVecN, UnboundedVecN};
use candid::Principal;
use ic_stable_structures::storable::{Blob, Storable};
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
        let size = rng.rand_u32() % Self::MAX_SIZE;
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

impl Random for Principal {
    fn random(rng: &mut Rng) -> Self {
        let size = 1 + (rng.rand_u32() % (Principal::MAX_LENGTH_IN_BYTES as u32 - 1));
        let mut buf = Vec::with_capacity(size as usize);
        for _ in 0..size {
            buf.push(rng.rand_u8());
        }
        Principal::from_slice(&buf)
    }
}

impl Random for () {
    fn random(_: &mut Rng) -> Self {}
}
