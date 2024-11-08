use ic_stable_structures::storable::{Blob, Storable};
use tiny_rng::{Rand, Rng};

mod btreemap;
mod memory_manager;
mod vec;

trait Random {
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

impl Random for u64 {
    fn random(rng: &mut Rng) -> Self {
        rng.rand_u64()
    }
}

fn main() {}
