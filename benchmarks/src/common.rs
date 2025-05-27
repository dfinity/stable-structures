use ic_stable_structures::storable::{Blob, BoundedVecN, Storable, UnboundedVecN};
use std::convert::{From, TryFrom};
use tiny_rng::{Rand, Rng};

pub trait Random {
    fn random(rng: &mut Rng) -> Self;
}

fn random_bytes(rng: &mut Rng, max_size: u32) -> Vec<u8> {
    let size = if max_size > 0 {
        (rng.rand_u32() % max_size) as usize
    } else {
        0
    };
    rng.iter(Rand::rand_u8).take(size).collect()
}

impl<const K: usize> Random for Blob<K> {
    fn random(rng: &mut Rng) -> Self {
        let bytes = random_bytes(rng, Blob::<K>::BOUND.max_size());
        Blob::try_from(&bytes[..]).unwrap()
    }
}

impl<const K: usize> Random for UnboundedVecN<K> {
    fn random(rng: &mut Rng) -> Self {
        let bytes = random_bytes(rng, Self::max_size());
        Self::from(&bytes[..])
    }
}

impl<const K: usize> Random for BoundedVecN<K> {
    fn random(rng: &mut Rng) -> Self {
        let bytes = random_bytes(rng, Self::max_size());
        Self::from(&bytes[..])
    }
}

impl Random for u64 {
    fn random(rng: &mut Rng) -> Self {
        rng.rand_u64()
    }
}
