use std::ops::Bound;

use crate::Random;
use canbench::{benchmark, macros::bench, BenchResult};
use ic_stable_structures::{storable::Blob, BTreeMap, DefaultMemoryImpl, Storable};
use tiny_rng::{Rand, Rng};

#[bench]
pub fn btreemap_insert_blob_4_1024() -> BenchResult {
    insert_blob_helper::<4, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_4_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<4, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_8_1024() -> BenchResult {
    insert_blob_helper::<8, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_8_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<8, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_16_1024() -> BenchResult {
    insert_blob_helper::<16, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_16_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<16, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_32_1024() -> BenchResult {
    insert_blob_helper::<32, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_32_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<32, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_64_1024() -> BenchResult {
    insert_blob_helper::<64, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_64_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<64, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_128_1024() -> BenchResult {
    insert_blob_helper::<128, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_128_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<128, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_256_1024() -> BenchResult {
    insert_blob_helper::<256, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_256_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<256, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_512_1024() -> BenchResult {
    insert_blob_helper::<512, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_512_1024_v2() -> BenchResult {
    insert_blob_helper_v2::<512, 1024>()
}

#[bench]
pub fn btreemap_insert_blob_1024_4() -> BenchResult {
    insert_blob_helper::<1024, 4>()
}

#[bench]
pub fn btreemap_insert_blob_1024_4_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 4>()
}

#[bench]
pub fn btreemap_insert_blob_1024_8() -> BenchResult {
    insert_blob_helper::<1024, 8>()
}

#[bench]
pub fn btreemap_insert_blob_1024_8_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 8>()
}

#[bench]
pub fn btreemap_insert_blob_1024_16() -> BenchResult {
    insert_blob_helper::<1024, 16>()
}

#[bench]
pub fn btreemap_insert_blob_1024_16_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 16>()
}

#[bench]
pub fn btreemap_insert_blob_1024_32() -> BenchResult {
    insert_blob_helper::<1024, 32>()
}

#[bench]
pub fn btreemap_insert_blob_1024_32_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 32>()
}

#[bench]
pub fn btreemap_insert_blob_1024_64() -> BenchResult {
    insert_blob_helper::<1024, 64>()
}

#[bench]
pub fn btreemap_insert_blob_1024_64_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 64>()
}

#[bench]
pub fn btreemap_insert_blob_1024_128() -> BenchResult {
    insert_blob_helper::<1024, 128>()
}

#[bench]
pub fn btreemap_insert_blob_1024_128_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 128>()
}

#[bench]
pub fn btreemap_insert_blob_1024_256() -> BenchResult {
    insert_blob_helper::<1024, 256>()
}

#[bench]
pub fn btreemap_insert_blob_1024_256_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 256>()
}

#[bench]
pub fn btreemap_insert_blob_1024_512() -> BenchResult {
    insert_blob_helper::<1024, 512>()
}

#[bench]
pub fn btreemap_insert_blob_1024_512_v2() -> BenchResult {
    insert_blob_helper_v2::<1024, 512>()
}

#[bench]
pub fn btreemap_insert_u64_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<u64, u64>(btree)
}

#[bench]
pub fn btreemap_insert_u64_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<u64, u64>(btree)
}

#[bench]
pub fn btreemap_insert_u64_blob_8() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<u64, Blob<8>>(btree)
}

#[bench]
pub fn btreemap_insert_u64_blob_8_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<u64, Blob<8>>(btree)
}

#[bench]
pub fn btreemap_insert_blob_8_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<Blob<8>, u64>(btree)
}

#[bench]
pub fn btreemap_insert_blob_8_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<Blob<8>, u64>(btree)
}

#[bench]
pub fn btreemap_insert_10mib_values() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());

    // Insert 200 10MiB values.
    let mut rng = Rng::from_seed(0);
    let mut values = vec![];
    for _ in 0..200 {
        values.push(rng.iter(Rand::rand_u8).take(10 * 1024).collect::<Vec<_>>());
    }

    benchmark(|| {
        let mut i = 0u64;
        for value in values.into_iter() {
            btree.insert(i, value);
            i += 1;
        }
    })
}

#[bench]
pub fn btreemap_iter_count_small_values() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let size: u8 = 200;
    for i in 0..size {
        btree.insert(i, i);
    }

    benchmark(|| {
        for i in 0..size {
            for j in i + 1..size {
                btree
                    .range((Bound::Included(i), Bound::Included(j)))
                    .count();
            }
        }
    })
}

#[bench]
pub fn btreemap_iter_count_10mib_values() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());

    // Insert 200 10MiB values.
    let mut rng = Rng::from_seed(0);
    let mut values = vec![];
    for _ in 0..200 {
        values.push(rng.iter(Rand::rand_u8).take(10 * 1024).collect::<Vec<_>>());
    }

    let mut i = 0u8;
    for value in values.into_iter() {
        btree.insert(i, value);
        i += 1;
    }

    benchmark(|| {
        for j in 0..i {
            for k in j + 1..i {
                btree
                    .range((Bound::Included(j), Bound::Included(k)))
                    .count();
            }
        }
    })
}

/// Benchmarks removing keys from a BTreeMap.
#[bench]
pub fn btreemap_remove_blob_4_1024() -> BenchResult {
    remove_blob_helper::<4, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_4_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<4, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_8_1024() -> BenchResult {
    remove_blob_helper::<8, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_8_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<8, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_16_1024() -> BenchResult {
    remove_blob_helper::<16, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_16_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<16, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_32_1024() -> BenchResult {
    remove_blob_helper::<32, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_32_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<32, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_64_1024() -> BenchResult {
    remove_blob_helper::<64, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_64_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<64, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_128_1024() -> BenchResult {
    remove_blob_helper::<128, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_128_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<128, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_256_1024() -> BenchResult {
    remove_blob_helper::<256, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_256_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<256, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_512_1024() -> BenchResult {
    remove_blob_helper::<512, 1024>()
}

#[bench]
pub fn btreemap_remove_blob_512_1024_v2() -> BenchResult {
    remove_blob_helper_v2::<512, 1024>()
}

#[bench]
pub fn btreemap_remove_u64_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<u64, u64>(btree)
}
#[bench]
pub fn btreemap_remove_u64_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<u64, u64>(btree)
}

#[bench]
pub fn btreemap_remove_u64_blob_8() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<u64, Blob<8>>(btree)
}
#[bench]
pub fn btreemap_remove_u64_blob_8_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<u64, Blob<8>>(btree)
}

#[bench]
pub fn btreemap_remove_blob_8_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<Blob<8>, u64>(btree)
}
#[bench]
pub fn btreemap_remove_blob_8_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<Blob<8>, u64>(btree)
}

/// Benchmarks getting keys from a BTreeMap.
#[bench]
pub fn btreemap_get_blob_4_1024() -> BenchResult {
    get_blob_helper::<4, 1024>()
}

#[bench]
pub fn btreemap_get_blob_4_1024_v2() -> BenchResult {
    get_blob_helper_v2::<4, 1024>()
}

#[bench]
pub fn btreemap_get_blob_8_1024() -> BenchResult {
    get_blob_helper::<8, 1024>()
}

#[bench]
pub fn btreemap_get_blob_8_1024_v2() -> BenchResult {
    get_blob_helper_v2::<8, 1024>()
}

#[bench]
pub fn btreemap_get_blob_16_1024() -> BenchResult {
    get_blob_helper::<16, 1024>()
}

#[bench]
pub fn btreemap_get_blob_16_1024_v2() -> BenchResult {
    get_blob_helper_v2::<16, 1024>()
}

#[bench]
pub fn btreemap_get_blob_32_1024() -> BenchResult {
    get_blob_helper::<32, 1024>()
}

#[bench]
pub fn btreemap_get_blob_32_1024_v2() -> BenchResult {
    get_blob_helper_v2::<32, 1024>()
}

#[bench]
pub fn btreemap_get_blob_64_1024() -> BenchResult {
    get_blob_helper::<64, 1024>()
}

#[bench]
pub fn btreemap_get_blob_64_1024_v2() -> BenchResult {
    get_blob_helper_v2::<64, 1024>()
}

#[bench]
pub fn btreemap_get_blob_128_1024() -> BenchResult {
    get_blob_helper::<128, 1024>()
}

#[bench]
pub fn btreemap_get_blob_128_1024_v2() -> BenchResult {
    get_blob_helper_v2::<128, 1024>()
}

#[bench]
pub fn btreemap_get_blob_256_1024() -> BenchResult {
    get_blob_helper::<256, 1024>()
}

#[bench]
pub fn btreemap_get_blob_256_1024_v2() -> BenchResult {
    get_blob_helper_v2::<256, 1024>()
}

#[bench]
pub fn btreemap_get_blob_512_1024() -> BenchResult {
    get_blob_helper::<512, 1024>()
}

#[bench]
pub fn btreemap_get_blob_512_1024_v2() -> BenchResult {
    get_blob_helper_v2::<512, 1024>()
}

#[bench]
pub fn btreemap_get_u64_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<u64, u64>(btree)
}

#[bench]
pub fn btreemap_get_u64_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<u64, u64>(btree)
}

#[bench]
pub fn btreemap_get_u64_blob_8() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<u64, Blob<8>>(btree)
}

#[bench]
pub fn btreemap_get_u64_blob_8_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<u64, Blob<8>>(btree)
}

#[bench]
pub fn btreemap_get_blob_8_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<Blob<8>, u64>(btree)
}

#[bench]
pub fn btreemap_get_blob_8_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<Blob<8>, u64>(btree)
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_blob_helper<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<Blob<K>, Blob<V>>(btree)
}

fn insert_blob_helper_v2<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<Blob<K>, Blob<V>>(btree)
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, DefaultMemoryImpl>,
) -> BenchResult {
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        random_keys.push(K::random(&mut rng));
        random_values.push(V::random(&mut rng));
    }

    benchmark(|| {
        // Insert the keys into the btree.
        for (k, v) in random_keys.into_iter().zip(random_values.into_iter()) {
            btree.insert(k, v);
        }
    })
}

// Profiles getting a large number of random blobs from a btreemap.
fn get_blob_helper<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<Blob<K>, Blob<V>>(btree)
}

fn get_blob_helper_v2<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<Blob<K>, Blob<V>>(btree)
}

fn get_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, DefaultMemoryImpl>,
) -> BenchResult {
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
    benchmark(|| {
        for k in random_keys.into_iter() {
            btree.get(&k).unwrap();
        }
    })
}

// Inserts a large number of random blobs into a btreemap, then profiles removing them.
fn remove_blob_helper<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<Blob<K>, Blob<V>>(btree)
}

fn remove_blob_helper_v2<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<Blob<K>, Blob<V>>(btree)
}

fn remove_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, DefaultMemoryImpl>,
) -> BenchResult {
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

    benchmark(|| {
        // Remove the keys from the btree.
        for k in random_keys.into_iter() {
            btree.remove(&k);
        }
    })
}
