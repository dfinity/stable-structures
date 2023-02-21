use crate::count_instructions;
use ic_cdk_macros::{query, update};
use ic_stable_structures::storable::Blob;
use ic_stable_structures::{DefaultMemoryImpl, StableVec};
use tiny_rng::{Rand, Rng};

#[update]
pub fn vec_insert_blob_4() -> u64 {
    vec_insert_blob::<4>()
}

#[update]
pub fn vec_insert_blob_8() -> u64 {
    vec_insert_blob::<8>()
}

#[update]
pub fn vec_insert_blob_16() -> u64 {
    vec_insert_blob::<16>()
}

#[update]
pub fn vec_insert_blob_32() -> u64 {
    vec_insert_blob::<32>()
}

#[update]
pub fn vec_insert_blob_64() -> u64 {
    vec_insert_blob::<64>()
}

#[update]
pub fn vec_insert_blob_128() -> u64 {
    vec_insert_blob::<128>()
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

fn vec_insert_blob<const N: usize>() -> u64 {
    let num_items = 10_000;
    let svec: StableVec<Blob<N>, _> = StableVec::new(DefaultMemoryImpl::default()).unwrap();

    let mut rng = Rng::from_seed(0);
    let mut random_items = Vec::with_capacity(num_items);

    for _ in 0..num_items {
        let key_size = rng.rand_u32() % (N as u32 + 1);
        random_items.push(Blob::try_from(random_vec(&mut rng, key_size).as_slice()).unwrap());
    }

    count_instructions(|| {
        for item in random_items.iter() {
            svec.push(item).unwrap();
        }
    })
}

fn vec_get_blob<const N: usize>() -> u64 {
    let num_items = 10_000;
    let svec: StableVec<Blob<N>, _> = StableVec::new(DefaultMemoryImpl::default()).unwrap();

    let mut rng = Rng::from_seed(0);

    for _ in 0..num_items {
        let key_size = rng.rand_u32() % (N as u32 + 1);
        svec.push(&Blob::try_from(random_vec(&mut rng, key_size).as_slice()).unwrap())
            .unwrap();
    }

    count_instructions(|| {
        for i in 0..num_items {
            svec.get(i as u64).unwrap();
        }
    })
}

fn random_vec(rng: &mut Rng, len: u32) -> Vec<u8> {
    rng.iter(Rand::rand_u8).take(len as usize).collect()
}
