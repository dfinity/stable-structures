use crate::Random;
use canbench::{benchmark, macros::bench, BenchResult};
use ic_stable_structures::storable::Blob;
use ic_stable_structures::{DefaultMemoryImpl, StableVec, Storable};
use tiny_rng::{Rand, Rng};

#[bench]
pub fn vec_insert_blob_4() -> BenchResult {
    vec_insert_blob::<4>()
}

#[bench]
pub fn vec_insert_blob_8() -> BenchResult {
    vec_insert_blob::<8>()
}

#[bench]
pub fn vec_insert_blob_16() -> BenchResult {
    vec_insert_blob::<16>()
}

#[bench]
pub fn vec_insert_blob_32() -> BenchResult {
    vec_insert_blob::<32>()
}

#[bench]
pub fn vec_insert_blob_64() -> BenchResult {
    vec_insert_blob::<64>()
}

#[bench]
pub fn vec_insert_blob_128() -> BenchResult {
    vec_insert_blob::<128>()
}

#[bench]
pub fn vec_insert_u64() -> BenchResult {
    vec_insert::<u64>()
}

#[bench]
pub fn vec_get_blob_4() -> BenchResult {
    vec_get_blob::<4>()
}

#[bench]
pub fn vec_get_blob_8() -> BenchResult {
    vec_get_blob::<8>()
}

#[bench]
pub fn vec_get_blob_16() -> BenchResult {
    vec_get_blob::<16>()
}

#[bench]
pub fn vec_get_blob_32() -> BenchResult {
    vec_get_blob::<32>()
}

#[bench]
pub fn vec_get_blob_64() -> BenchResult {
    vec_get_blob::<64>()
}

#[bench]
pub fn vec_get_blob_128() -> BenchResult {
    vec_get_blob::<128>()
}

#[bench]
pub fn vec_get_u64() -> BenchResult {
    vec_get::<u64>()
}

fn vec_insert_blob<const N: usize>() -> BenchResult {
    vec_insert::<Blob<N>>()
}

fn vec_insert<T: Storable + Random>() -> BenchResult {
    let num_items = 10_000;
    let svec: StableVec<T, _> = StableVec::new(DefaultMemoryImpl::default()).unwrap();

    let mut rng = Rng::from_seed(0);
    let mut random_items = Vec::with_capacity(num_items);

    for _ in 0..num_items {
        random_items.push(T::random(&mut rng));
    }

    benchmark(|| {
        for item in random_items.iter() {
            svec.push(item).unwrap();
        }
    })
}

fn vec_get_blob<const N: usize>() -> BenchResult {
    vec_get::<Blob<N>>()
}

fn vec_get<T: Storable + Random>() -> BenchResult {
    let num_items = 10_000;
    let svec: StableVec<T, _> = StableVec::new(DefaultMemoryImpl::default()).unwrap();

    let mut rng = Rng::from_seed(0);

    for _ in 0..num_items {
        svec.push(&T::random(&mut rng)).unwrap();
    }

    benchmark(|| {
        for i in 0..num_items {
            svec.get(i as u64).unwrap();
        }
    })
}
