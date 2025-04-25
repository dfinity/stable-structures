use crate::Random;
use canbench_rs::{bench, bench_fn, BenchResult};
use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
use tiny_rng::{Rand, Rng};

#[bench(raw)]
pub fn btreeset_insert_10k_elements() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());

    bench_fn(|| {
        for i in 0..10_000 {
            btreeset.insert(i);
        }
    })
}

#[bench(raw)]
pub fn btreeset_remove_10k_elements() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());

    for i in 0..10_000 {
        btreeset.insert(i);
    }

    bench_fn(|| {
        for i in 0..10_000 {
            btreeset.remove(&i);
        }
    })
}

#[bench(raw)]
pub fn btreeset_iterate_10k_elements() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());

    for i in 0..10_000 {
        btreeset.insert(i);
    }

    bench_fn(|| for _ in btreeset.iter() {})
}

#[bench(raw)]
pub fn btreeset_range_query() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());

    for i in 0..10_000 {
        btreeset.insert(i);
    }

    bench_fn(|| for _ in btreeset.range(2000..8000) {})
}
