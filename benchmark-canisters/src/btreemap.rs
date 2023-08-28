use crate::{count_instructions, Random};
use ic_cdk_macros::query;
use ic_stable_structures::{storable::Blob, BTreeMap, DefaultMemoryImpl, Storable};
use tiny_rng::{Rand, Rng};

#[query]
pub fn btreemap_insert_blob_4_1024() -> u64 {
    insert_blob_helper::<4, 1024>()
}

#[query]
pub fn btreemap_insert_blob_4_1024_v2() -> u64 {
    insert_blob_helper_v2::<4, 1024>()
}

#[query]
pub fn btreemap_insert_blob_8_1024() -> u64 {
    insert_blob_helper::<8, 1024>()
}

#[query]
pub fn btreemap_insert_blob_8_1024_v2() -> u64 {
    insert_blob_helper_v2::<8, 1024>()
}

#[query]
pub fn btreemap_insert_blob_16_1024() -> u64 {
    insert_blob_helper::<16, 1024>()
}

#[query]
pub fn btreemap_insert_blob_16_1024_v2() -> u64 {
    insert_blob_helper_v2::<16, 1024>()
}

#[query]
pub fn btreemap_insert_blob_32_1024() -> u64 {
    insert_blob_helper::<32, 1024>()
}

#[query]
pub fn btreemap_insert_blob_32_1024_v2() -> u64 {
    insert_blob_helper_v2::<32, 1024>()
}

#[query]
pub fn btreemap_insert_blob_64_1024() -> u64 {
    insert_blob_helper::<64, 1024>()
}

#[query]
pub fn btreemap_insert_blob_64_1024_v2() -> u64 {
    insert_blob_helper_v2::<64, 1024>()
}

#[query]
pub fn btreemap_insert_blob_128_1024() -> u64 {
    insert_blob_helper::<128, 1024>()
}

#[query]
pub fn btreemap_insert_blob_128_1024_v2() -> u64 {
    insert_blob_helper_v2::<128, 1024>()
}

#[query]
pub fn btreemap_insert_blob_256_1024() -> u64 {
    insert_blob_helper::<256, 1024>()
}

#[query]
pub fn btreemap_insert_blob_256_1024_v2() -> u64 {
    insert_blob_helper_v2::<256, 1024>()
}

#[query]
pub fn btreemap_insert_blob_512_1024() -> u64 {
    insert_blob_helper::<512, 1024>()
}

#[query]
pub fn btreemap_insert_blob_512_1024_v2() -> u64 {
    insert_blob_helper_v2::<512, 1024>()
}

#[query]
pub fn btreemap_insert_blob_1024_4() -> u64 {
    insert_blob_helper::<1024, 4>()
}

#[query]
pub fn btreemap_insert_blob_1024_4_v2() -> u64 {
    insert_blob_helper_v2::<1024, 4>()
}

#[query]
pub fn btreemap_insert_blob_1024_8() -> u64 {
    insert_blob_helper::<1024, 8>()
}

#[query]
pub fn btreemap_insert_blob_1024_8_v2() -> u64 {
    insert_blob_helper_v2::<1024, 8>()
}

#[query]
pub fn btreemap_insert_blob_1024_16() -> u64 {
    insert_blob_helper::<1024, 16>()
}

#[query]
pub fn btreemap_insert_blob_1024_16_v2() -> u64 {
    insert_blob_helper_v2::<1024, 16>()
}

#[query]
pub fn btreemap_insert_blob_1024_32() -> u64 {
    insert_blob_helper::<1024, 32>()
}

#[query]
pub fn btreemap_insert_blob_1024_32_v2() -> u64 {
    insert_blob_helper_v2::<1024, 32>()
}

#[query]
pub fn btreemap_insert_blob_1024_64() -> u64 {
    insert_blob_helper::<1024, 64>()
}

#[query]
pub fn btreemap_insert_blob_1024_64_v2() -> u64 {
    insert_blob_helper_v2::<1024, 64>()
}

#[query]
pub fn btreemap_insert_blob_1024_128() -> u64 {
    insert_blob_helper::<1024, 128>()
}

#[query]
pub fn btreemap_insert_blob_1024_128_v2() -> u64 {
    insert_blob_helper_v2::<1024, 128>()
}

#[query]
pub fn btreemap_insert_blob_1024_256() -> u64 {
    insert_blob_helper::<1024, 256>()
}

#[query]
pub fn btreemap_insert_blob_1024_256_v2() -> u64 {
    insert_blob_helper_v2::<1024, 256>()
}

#[query]
pub fn btreemap_insert_blob_1024_512() -> u64 {
    insert_blob_helper::<1024, 512>()
}

#[query]
pub fn btreemap_insert_blob_1024_512_v2() -> u64 {
    insert_blob_helper_v2::<1024, 512>()
}

#[query]
pub fn btreemap_insert_u64_u64() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<u64, u64>(btree)
}

#[query]
pub fn btreemap_insert_u64_u64_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    insert_helper::<u64, u64>(btree)
}

#[query]
pub fn btreemap_insert_u64_blob_8() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<u64, Blob<8>>(btree)
}

#[query]
pub fn btreemap_insert_u64_blob_8_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    insert_helper::<u64, Blob<8>>(btree)
}

#[query]
pub fn btreemap_insert_blob_8_u64() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<Blob<8>, u64>(btree)
}

#[query]
pub fn btreemap_insert_blob_8_u64_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    insert_helper::<Blob<8>, u64>(btree)
}

/// Benchmarks removing keys from a BTreeMap.
#[query]
pub fn btreemap_remove_blob_4_1024() -> u64 {
    remove_blob_helper::<4, 1024>()
}

#[query]
pub fn btreemap_remove_blob_4_1024_v2() -> u64 {
    remove_blob_helper_v2::<4, 1024>()
}

#[query]
pub fn btreemap_remove_blob_8_1024() -> u64 {
    remove_blob_helper::<8, 1024>()
}

#[query]
pub fn btreemap_remove_blob_8_1024_v2() -> u64 {
    remove_blob_helper_v2::<8, 1024>()
}

#[query]
pub fn btreemap_remove_blob_16_1024() -> u64 {
    remove_blob_helper::<16, 1024>()
}

#[query]
pub fn btreemap_remove_blob_16_1024_v2() -> u64 {
    remove_blob_helper_v2::<16, 1024>()
}

#[query]
pub fn btreemap_remove_blob_32_1024() -> u64 {
    remove_blob_helper::<32, 1024>()
}

#[query]
pub fn btreemap_remove_blob_32_1024_v2() -> u64 {
    remove_blob_helper_v2::<32, 1024>()
}

#[query]
pub fn btreemap_remove_blob_64_1024() -> u64 {
    remove_blob_helper::<64, 1024>()
}

#[query]
pub fn btreemap_remove_blob_64_1024_v2() -> u64 {
    remove_blob_helper_v2::<64, 1024>()
}

#[query]
pub fn btreemap_remove_blob_128_1024() -> u64 {
    remove_blob_helper::<128, 1024>()
}

#[query]
pub fn btreemap_remove_blob_128_1024_v2() -> u64 {
    remove_blob_helper_v2::<128, 1024>()
}

#[query]
pub fn btreemap_remove_blob_256_1024() -> u64 {
    remove_blob_helper::<256, 1024>()
}

#[query]
pub fn btreemap_remove_blob_256_1024_v2() -> u64 {
    remove_blob_helper_v2::<256, 1024>()
}

#[query]
pub fn btreemap_remove_blob_512_1024() -> u64 {
    remove_blob_helper::<512, 1024>()
}

#[query]
pub fn btreemap_remove_blob_512_1024_v2() -> u64 {
    remove_blob_helper_v2::<512, 1024>()
}

#[query]
pub fn btreemap_remove_u64_u64() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<u64, u64>(btree)
}
#[query]
pub fn btreemap_remove_u64_u64_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    remove_helper::<u64, u64>(btree)
}

#[query]
pub fn btreemap_remove_u64_blob_8() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<u64, Blob<8>>(btree)
}
#[query]
pub fn btreemap_remove_u64_blob_8_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    remove_helper::<u64, Blob<8>>(btree)
}

#[query]
pub fn btreemap_remove_blob_8_u64() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<Blob<8>, u64>(btree)
}
#[query]
pub fn btreemap_remove_blob_8_u64_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    remove_helper::<Blob<8>, u64>(btree)
}

/// Benchmarks getting keys from a BTreeMap.
#[query]
pub fn btreemap_get_blob_4_1024() -> u64 {
    get_blob_helper::<4, 1024>()
}

#[query]
pub fn btreemap_get_blob_4_1024_v2() -> u64 {
    get_blob_helper_v2::<4, 1024>()
}

#[query]
pub fn btreemap_get_blob_8_1024() -> u64 {
    get_blob_helper::<8, 1024>()
}

#[query]
pub fn btreemap_get_blob_8_1024_v2() -> u64 {
    get_blob_helper_v2::<8, 1024>()
}

#[query]
pub fn btreemap_get_blob_16_1024() -> u64 {
    get_blob_helper::<16, 1024>()
}

#[query]
pub fn btreemap_get_blob_16_1024_v2() -> u64 {
    get_blob_helper_v2::<16, 1024>()
}

#[query]
pub fn btreemap_get_blob_32_1024() -> u64 {
    get_blob_helper::<32, 1024>()
}

#[query]
pub fn btreemap_get_blob_32_1024_v2() -> u64 {
    get_blob_helper_v2::<32, 1024>()
}

#[query]
pub fn btreemap_get_blob_64_1024() -> u64 {
    get_blob_helper::<64, 1024>()
}

#[query]
pub fn btreemap_get_blob_64_1024_v2() -> u64 {
    get_blob_helper_v2::<64, 1024>()
}

#[query]
pub fn btreemap_get_blob_128_1024() -> u64 {
    get_blob_helper::<128, 1024>()
}

#[query]
pub fn btreemap_get_blob_128_1024_v2() -> u64 {
    get_blob_helper_v2::<128, 1024>()
}

#[query]
pub fn btreemap_get_blob_256_1024() -> u64 {
    get_blob_helper::<256, 1024>()
}

#[query]
pub fn btreemap_get_blob_256_1024_v2() -> u64 {
    get_blob_helper_v2::<256, 1024>()
}

#[query]
pub fn btreemap_get_blob_512_1024() -> u64 {
    get_blob_helper::<512, 1024>()
}

#[query]
pub fn btreemap_get_blob_512_1024_v2() -> u64 {
    get_blob_helper_v2::<512, 1024>()
}

#[query]
pub fn btreemap_get_u64_u64() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<u64, u64>(btree)
}

#[query]
pub fn btreemap_get_u64_u64_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    get_helper::<u64, u64>(btree)
}

#[query]
pub fn btreemap_get_u64_blob_8() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<u64, Blob<8>>(btree)
}

#[query]
pub fn btreemap_get_u64_blob_8_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    get_helper::<u64, Blob<8>>(btree)
}

#[query]
pub fn btreemap_get_blob_8_u64() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<Blob<8>, u64>(btree)
}

#[query]
pub fn btreemap_get_blob_8_u64_v2() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    get_helper::<Blob<8>, u64>(btree)
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_blob_helper<const K: usize, const V: usize>() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<Blob<K>, Blob<V>>(btree)
}

fn insert_blob_helper_v2<const K: usize, const V: usize>() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    insert_helper::<Blob<K>, Blob<V>>(btree)
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, DefaultMemoryImpl>,
) -> u64 {
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        random_keys.push(K::random(&mut rng));
        random_values.push(V::random(&mut rng));
    }

    count_instructions(|| {
        // Insert the keys into the btree.
        for (k, v) in random_keys.into_iter().zip(random_values.into_iter()) {
            btree.insert(k, v);
        }
    })
}

// Profiles getting a large number of random blobs from a btreemap.
fn get_blob_helper<const K: usize, const V: usize>() -> u64 {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<Blob<K>, Blob<V>>(btree)
}

fn get_blob_helper_v2<const K: usize, const V: usize>() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    get_helper::<Blob<K>, Blob<V>>(btree)
}

fn get_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, DefaultMemoryImpl>,
) -> u64 {
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        random_keys.push(K::random(&mut rng));
        random_values.push(V::random(&mut rng));
    }

    // Insert the keys into the btree.
    for (k, v) in random_keys.iter().zip(random_values.into_iter()) {
        btree.insert(k.clone(), v);
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
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<Blob<K>, Blob<V>>(btree)
}

fn remove_blob_helper_v2<const K: usize, const V: usize>() -> u64 {
    let btree = BTreeMap::new_v2(DefaultMemoryImpl::default());
    remove_helper::<Blob<K>, Blob<V>>(btree)
}

fn remove_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, DefaultMemoryImpl>,
) -> u64 {
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        random_keys.push(K::random(&mut rng));
        random_values.push(V::random(&mut rng));
    }

    // Insert the keys into the btree.
    for (k, v) in random_keys.iter().zip(random_values.into_iter()) {
        btree.insert(k.clone(), v);
    }

    count_instructions(|| {
        // Remove the keys from the btree.
        for k in random_keys.into_iter() {
            btree.remove(&k);
        }
    })
}
