use ic_stable_structures::storable::{Blob, FixedVec, Storable};
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

impl<const K: usize> Random for FixedVec<K> {
    fn random(rng: &mut Rng) -> Self {
        let size = rng.rand_u32() % Self::max_size();
        let mut buf = Vec::with_capacity(size as usize);
        for _ in 0..size {
            buf.push(rng.rand_u8());
        }
        FixedVec::from(&buf)
    }
}

impl Random for u64 {
    fn random(rng: &mut Rng) -> Self {
        rng.rand_u64()
    }
}
