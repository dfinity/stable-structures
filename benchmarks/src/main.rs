use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
use tiny_rng::{Rand, Rng};

/// Benchmarks inserting 1000 keys into a BTreeMap.
#[ic_cdk_macros::query]
pub fn btreemap_insert() -> u64 {
    let mut btree: BTreeMap<_, u64, ()> = BTreeMap::init(DefaultMemoryImpl::default());

    // Generate 1000 keys
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(1000);
    for _ in 0..1_000 {
        random_keys.push(rng.rand_u64());
    }

    count_instructions(|| {
        // Insert the keys in to the btree.
        for k in random_keys.into_iter() {
            btree.insert(k, ()).unwrap();
        }
    })
}

/// Benchmarks removing 1000 keys from a BTreeMap.
#[ic_cdk_macros::query]
pub fn btreemap_remove() -> u64 {
    let mut btree: BTreeMap<_, u64, ()> = BTreeMap::init(DefaultMemoryImpl::default());

    // Generate 1000 keys
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(1000);
    for _ in 0..1_000 {
        random_keys.push(rng.rand_u64());
    }

    for k in random_keys.clone().into_iter() {
        btree.insert(k, ()).unwrap();
    }

    count_instructions(|| {
        // Remove the keys from the btree.
        for k in random_keys.into_iter() {
            btree.remove(&k).unwrap();
        }
    })
}

fn count_instructions<R>(f: impl FnOnce() -> R) -> u64 {
    let start = ic_cdk::api::performance_counter(0);
    f();
    ic_cdk::api::performance_counter(0) - start
}

fn main() {}
