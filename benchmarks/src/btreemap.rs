use crate::count_instructions;
use ic_cdk_macros::{query, update};
use ic_stable_structures::{storable::Blob, BTreeMap, BoundedStorable, DefaultMemoryImpl};
use tiny_rng::{Rand, Rng};

#[query]
pub fn btreemap_insert_blob_4_1024() -> u64 {
    insert_blob_helper::<4, 1024>()
}

#[query]
pub fn btreemap_insert_blob_8_1024() -> u64 {
    insert_blob_helper::<8, 1024>()
}

#[query]
pub fn btreemap_insert_blob_16_1024() -> u64 {
    insert_blob_helper::<16, 1024>()
}

#[query]
pub fn btreemap_insert_blob_32_1024() -> u64 {
    insert_blob_helper::<32, 1024>()
}

#[query]
pub fn btreemap_insert_blob_64_1024() -> u64 {
    insert_blob_helper::<64, 1024>()
}

#[query]
pub fn btreemap_insert_blob_128_1024() -> u64 {
    insert_blob_helper::<128, 1024>()
}

#[update]
pub fn btreemap_insert_blob_256_1024() -> u64 {
    insert_blob_helper::<256, 1024>()
}

#[update]
pub fn btreemap_insert_blob_512_1024() -> u64 {
    insert_blob_helper::<512, 1024>()
}

#[update]
pub fn btreemap_insert_blob_1024_4() -> u64 {
    insert_blob_helper::<1024, 4>()
}

#[update]
pub fn btreemap_insert_blob_1024_8() -> u64 {
    insert_blob_helper::<1024, 8>()
}

#[update]
pub fn btreemap_insert_blob_1024_16() -> u64 {
    insert_blob_helper::<1024, 16>()
}

#[update]
pub fn btreemap_insert_blob_1024_32() -> u64 {
    insert_blob_helper::<1024, 32>()
}

#[update]
pub fn btreemap_insert_blob_1024_64() -> u64 {
    insert_blob_helper::<1024, 64>()
}

#[update]
pub fn btreemap_insert_blob_1024_128() -> u64 {
    insert_blob_helper::<1024, 128>()
}

#[update]
pub fn btreemap_insert_blob_1024_256() -> u64 {
    insert_blob_helper::<1024, 256>()
}

#[update]
pub fn btreemap_insert_blob_1024_512() -> u64 {
    insert_blob_helper::<1024, 512>()
}

/// Benchmarks removing keys from a BTreeMap.
#[update]
pub fn btreemap_remove_blob_4_1024() -> u64 {
    remove_blob_helper::<4, 1024>()
}

#[update]
pub fn btreemap_remove_blob_8_1024() -> u64 {
    remove_blob_helper::<8, 1024>()
}

#[update]
pub fn btreemap_remove_blob_16_1024() -> u64 {
    remove_blob_helper::<16, 1024>()
}

#[update]
pub fn btreemap_remove_blob_32_1024() -> u64 {
    remove_blob_helper::<32, 1024>()
}

#[update]
pub fn btreemap_remove_blob_64_1024() -> u64 {
    remove_blob_helper::<64, 1024>()
}

#[update]
pub fn btreemap_remove_blob_128_1024() -> u64 {
    remove_blob_helper::<128, 1024>()
}

#[update]
pub fn btreemap_remove_blob_256_1024() -> u64 {
    remove_blob_helper::<256, 1024>()
}

#[update]
pub fn btreemap_remove_blob_512_1024() -> u64 {
    get_blob_helper::<512, 1024>()
}

/// Benchmarks getting keys from a BTreeMap.
#[query]
pub fn btreemap_get_blob_4_1024() -> u64 {
    get_blob_helper::<4, 1024>()
}

#[query]
pub fn btreemap_get_blob_8_1024() -> u64 {
    get_blob_helper::<8, 1024>()
}

#[query]
pub fn btreemap_get_blob_16_1024() -> u64 {
    get_blob_helper::<16, 1024>()
}

#[query]
pub fn btreemap_get_blob_32_1024() -> u64 {
    get_blob_helper::<32, 1024>()
}

#[query]
pub fn btreemap_get_blob_64_1024() -> u64 {
    get_blob_helper::<64, 1024>()
}

#[query]
pub fn btreemap_get_blob_128_1024() -> u64 {
    get_blob_helper::<128, 1024>()
}

#[query]
pub fn btreemap_get_blob_256_1024() -> u64 {
    get_blob_helper::<256, 1024>()
}

#[query]
pub fn btreemap_get_blob_512_1024() -> u64 {
    get_blob_helper::<512, 1024>()
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_blob_helper<const K: usize, const V: usize>() -> u64 {
    let mut btree: BTreeMap<Blob<K>, Blob<V>, _> = BTreeMap::new(DefaultMemoryImpl::default());
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        let key_size = rng.rand_u32() % Blob::<K>::MAX_SIZE;
        let value_size = rng.rand_u32() % Blob::<V>::MAX_SIZE;
        random_keys.push(random_vec(&mut rng, key_size));
        random_values.push(random_vec(&mut rng, value_size));
    }

    count_instructions(|| {
        // Insert the keys into the btree.
        for (k, v) in random_keys.into_iter().zip(random_values.into_iter()) {
            btree.insert(
                Blob::try_from(k.as_slice()).unwrap(),
                Blob::try_from(v.as_slice()).unwrap(),
            );
        }
    })
}

// Profiles getting a large number of random blobs from a btreemap.
fn get_blob_helper<const K: usize, const V: usize>() -> u64 {
    let mut btree: BTreeMap<Blob<K>, Blob<V>, _> = BTreeMap::new(DefaultMemoryImpl::default());
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        let key_size = rng.rand_u32() % Blob::<K>::MAX_SIZE;
        let value_size = rng.rand_u32() % Blob::<V>::MAX_SIZE;
        random_keys.push(Blob::try_from(random_vec(&mut rng, key_size).as_slice()).unwrap());
        random_values.push(Blob::try_from(random_vec(&mut rng, value_size).as_slice()).unwrap());
    }

    // Insert the keys into the btree.
    for (k, v) in random_keys.iter().zip(random_values.into_iter()) {
        btree.insert(*k, v);
    }

    // Get all the keys from the map.
    count_instructions(|| {
        for k in random_keys.into_iter() {
            btree.get(&k).unwrap();
        }
    })
}

// Inserts a large number of random blobs into a btreemap, then profiles removing them.
fn remove_blob_helper<const K: usize, const V: usize>() -> u64 {
    let mut btree: BTreeMap<Blob<K>, Blob<V>, _> = BTreeMap::new(DefaultMemoryImpl::default());
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        let key_size = rng.rand_u32() % Blob::<K>::MAX_SIZE;
        let value_size = rng.rand_u32() % Blob::<V>::MAX_SIZE;
        random_keys.push(Blob::try_from(random_vec(&mut rng, key_size).as_slice()).unwrap());
        random_values.push(Blob::try_from(random_vec(&mut rng, value_size).as_slice()).unwrap());
    }

    // Insert the keys into the btree.
    for (k, v) in random_keys.iter().zip(random_values.into_iter()) {
        btree.insert(*k, v);
    }

    count_instructions(|| {
        // Remove the keys from the btree.
        for k in random_keys.into_iter() {
            btree.remove(&k);
        }
    })
}

fn random_vec(rng: &mut Rng, len: u32) -> Vec<u8> {
    rng.iter(Rand::rand_u8).take(len as usize).collect()
}
