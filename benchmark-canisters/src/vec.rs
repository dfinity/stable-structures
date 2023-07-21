use crate::{count_instructions, Random};
use ic_cdk::query;
use ic_stable_structures::storable::Blob;
use ic_stable_structures::{BoundedStorable, DefaultMemoryImpl, StableVec};
use tiny_rng::{Rand, Rng};

#[query]
pub fn vec_insert_blob_4() -> u64 {
    vec_insert_blob::<4>()
}

#[query]
pub fn vec_insert_blob_8() -> u64 {
    vec_insert_blob::<8>()
}

#[query]
pub fn vec_insert_blob_16() -> u64 {
    vec_insert_blob::<16>()
}

#[query]
pub fn vec_insert_blob_32() -> u64 {
    vec_insert_blob::<32>()
}

#[query]
pub fn vec_insert_blob_64() -> u64 {
    vec_insert_blob::<64>()
}

#[query]
pub fn vec_insert_blob_128() -> u64 {
    vec_insert_blob::<128>()
}

#[query]
pub fn vec_insert_u64() -> u64 {
    vec_insert::<u64>()
}

#[query]
pub fn vec_get_blob_4() -> u64 {
    vec_get_blob::<4>()
}

#[query]
pub fn vec_get_blob_8() -> u64 {
    vec_get_blob::<8>()
}

#[query]
pub fn vec_get_blob_16() -> u64 {
    vec_get_blob::<16>()
}

#[query]
pub fn vec_get_blob_32() -> u64 {
    vec_get_blob::<32>()
}

#[query]
pub fn vec_get_blob_64() -> u64 {
    vec_get_blob::<64>()
}

#[query]
pub fn vec_get_blob_128() -> u64 {
    vec_get_blob::<128>()
}

#[query]
pub fn vec_get_u64() -> u64 {
    vec_get::<u64>()
}

fn vec_insert_blob<const N: usize>() -> u64 {
    vec_insert::<Blob<N>>()
}

fn vec_insert<T: BoundedStorable + Random>() -> u64 {
    let num_items = 10_000;
    let svec: StableVec<T, _> = StableVec::new(DefaultMemoryImpl::default()).unwrap();

    let mut rng = Rng::from_seed(0);
    let mut random_items = Vec::with_capacity(num_items);

    for _ in 0..num_items {
        random_items.push(T::random(&mut rng));
    }

    count_instructions(|| {
        for item in random_items.iter() {
            svec.push(item).unwrap();
        }
    })
}

fn vec_get_blob<const N: usize>() -> u64 {
    vec_get::<Blob<N>>()
}

fn vec_get<T: BoundedStorable + Random>() -> u64 {
    let num_items = 10_000;
    let svec: StableVec<T, _> = StableVec::new(DefaultMemoryImpl::default()).unwrap();

    let mut rng = Rng::from_seed(0);

    for _ in 0..num_items {
        svec.push(&T::random(&mut rng)).unwrap();
    }

    count_instructions(|| {
        for i in 0..num_items {
            svec.get(i as u64).unwrap();
        }
    })
}
