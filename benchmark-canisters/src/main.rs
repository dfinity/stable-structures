use candid::CandidType;
use ic_stable_structures::storable::{Blob, Bound, Storable};
use maplit::btreemap;
use serde::Deserialize;
use std::collections::BTreeMap;
use tiny_rng::{Rand, Rng};

mod btreemap;
mod memory_manager;
mod vec;

#[derive(Debug, PartialEq, Deserialize, CandidType)]
pub struct BenchResult {
    measurements: BTreeMap<String, u64>,
}

/// Benchmarks the given function.
pub(crate) fn benchmark<R>(f: impl FnOnce() -> R) -> BenchResult {
    let start = ic_cdk::api::performance_counter(0);
    profiler::reset();
    f();
    let total_instructions = ic_cdk::api::performance_counter(0) - start;

    let mut measurements = btreemap! {
        "instructions".to_string() => total_instructions,
        "stable_memory_size".to_string() => ic_cdk::api::stable::stable64_size()
    };

    let mut profiling_results: std::collections::BTreeMap<_, _> = profiler::get_results()
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect();

    measurements.append(&mut profiling_results);

    BenchResult { measurements }
}

const fn max_size<A: Storable>() -> u32 {
    if let Bound::Bounded { max_size, .. } = A::BOUND {
        max_size
    } else {
        panic!("Cannot get max size of unbounded type.");
    }
}

trait Random {
    fn random(rng: &mut Rng) -> Self;
}

impl<const K: usize> Random for Blob<K> {
    fn random(rng: &mut Rng) -> Self {
        let size = rng.rand_u32() % max_size::<Blob<K>>();
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
