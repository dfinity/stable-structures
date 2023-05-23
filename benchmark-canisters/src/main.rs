use ic_stable_structures::{storable::Blob, BoundedStorable};
use tiny_rng::{Rand, Rng};

mod btreemap;
mod memory_manager;
mod vec;

/// Returns the number of instructions consumed by the given function.
pub(crate) fn count_instructions<R>(f: impl FnOnce() -> R) -> u64 {
    let start = ic_cdk::api::performance_counter(0);
    f();
    ic_cdk::api::performance_counter(0) - start
}

trait Random {
    fn random(rng: &mut Rng) -> Self;
}

impl<const K: usize> Random for Blob<K> {
    fn random(rng: &mut Rng) -> Self {
        let size = rng.rand_u32() % Blob::<K>::MAX_SIZE;
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
