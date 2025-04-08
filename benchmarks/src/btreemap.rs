use crate::Random;
use canbench_rs::{bench, bench_fn, BenchResult};
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
use ic_stable_structures::{storable::Blob, BTreeMap, DefaultMemoryImpl, Memory, Storable};
use std::ops::Bound;
use tiny_rng::{Rand, Rng};

/// Helper macro to generate benchmarks.
macro_rules! bench_tests {
    ($( $fn_name:ident, $helper:ident, $k:expr, $v:expr );+ $(;)?) => {
        $(
            #[bench(raw)]
            pub fn $fn_name() -> BenchResult {
                $helper::<$k, $v>()
            }
        )+
    };
}

type Blob4 = Blob<4>;
type Blob8 = Blob<8>;
type Blob16 = Blob<16>;
type Blob32 = Blob<32>;
type Blob64 = Blob<64>;
type Blob128 = Blob<128>;
type Blob256 = Blob<256>;
type Blob512 = Blob<512>;
type Blob1024 = Blob<1024>;

// Benchmarks inserting blobs into a BTreeMap.
bench_tests! {
    // K x 1024
    btreemap_insert_blob_4_1024,       insert_helper_v1,    Blob4, Blob1024;
    btreemap_insert_blob_4_1024_v2,    insert_helper_v2,    Blob4, Blob1024;
    btreemap_insert_blob_8_1024,       insert_helper_v1,    Blob8, Blob1024;
    btreemap_insert_blob_8_1024_v2,    insert_helper_v2,    Blob8, Blob1024;
    btreemap_insert_blob_16_1024,      insert_helper_v1,   Blob16, Blob1024;
    btreemap_insert_blob_16_1024_v2,   insert_helper_v2,   Blob16, Blob1024;
    btreemap_insert_blob_32_1024,      insert_helper_v1,   Blob32, Blob1024;
    btreemap_insert_blob_32_1024_v2,   insert_helper_v2,   Blob32, Blob1024;
    btreemap_insert_blob_64_1024,      insert_helper_v1,   Blob64, Blob1024;
    btreemap_insert_blob_64_1024_v2,   insert_helper_v2,   Blob64, Blob1024;
    btreemap_insert_blob_128_1024,     insert_helper_v1,  Blob128, Blob1024;
    btreemap_insert_blob_128_1024_v2,  insert_helper_v2,  Blob128, Blob1024;
    btreemap_insert_blob_256_1024,     insert_helper_v1,  Blob256, Blob1024;
    btreemap_insert_blob_256_1024_v2,  insert_helper_v2,  Blob256, Blob1024;
    btreemap_insert_blob_512_1024,     insert_helper_v1,  Blob512, Blob1024;
    btreemap_insert_blob_512_1024_v2,  insert_helper_v2,  Blob512, Blob1024;

    // 1024 x V
    btreemap_insert_blob_1024_4,       insert_helper_v1, Blob1024,    Blob4;
    btreemap_insert_blob_1024_4_v2,    insert_helper_v2, Blob1024,    Blob4;
    btreemap_insert_blob_1024_8,       insert_helper_v1, Blob1024,    Blob8;
    btreemap_insert_blob_1024_8_v2,    insert_helper_v2, Blob1024,    Blob8;
    btreemap_insert_blob_1024_16,      insert_helper_v1, Blob1024,   Blob16;
    btreemap_insert_blob_1024_16_v2,   insert_helper_v2, Blob1024,   Blob16;
    btreemap_insert_blob_1024_32,      insert_helper_v1, Blob1024,   Blob32;
    btreemap_insert_blob_1024_32_v2,   insert_helper_v2, Blob1024,   Blob32;
    btreemap_insert_blob_1024_64,      insert_helper_v1, Blob1024,   Blob64;
    btreemap_insert_blob_1024_64_v2,   insert_helper_v2, Blob1024,   Blob64;
    btreemap_insert_blob_1024_128,     insert_helper_v1, Blob1024,  Blob128;
    btreemap_insert_blob_1024_128_v2,  insert_helper_v2, Blob1024,  Blob128;
    btreemap_insert_blob_1024_256,     insert_helper_v1, Blob1024,  Blob256;
    btreemap_insert_blob_1024_256_v2,  insert_helper_v2, Blob1024,  Blob256;
    btreemap_insert_blob_1024_512,     insert_helper_v1, Blob1024,  Blob512;
    btreemap_insert_blob_1024_512_v2,  insert_helper_v2, Blob1024,  Blob512;
    btreemap_insert_blob_1024_512_v2_mem_manager, insert_helper_v2_mem_manager, Blob1024, Blob512;

    btreemap_insert_u64_u64,           insert_helper_v1, u64,     u64;
    btreemap_insert_u64_u64_v2,        insert_helper_v2, u64,     u64;
    btreemap_insert_u64_u64_v2_mem_manager, insert_helper_v2_mem_manager, u64, u64;

    btreemap_insert_u64_blob_8,        insert_helper_v1, u64,   Blob8;
    btreemap_insert_u64_blob_8_v2,     insert_helper_v2, u64,   Blob8;
    btreemap_insert_blob_8_u64,        insert_helper_v1, Blob8,   u64;
    btreemap_insert_blob_8_u64_v2,     insert_helper_v2, Blob8,   u64;
}

// Benchmarks removing keys from a BTreeMap.
bench_tests! {
    // K x 1024
    btreemap_remove_blob_4_1024,        remove_helper_v1,     Blob4, Blob1024;
    btreemap_remove_blob_4_1024_v2,     remove_helper_v2,     Blob4, Blob1024;
    btreemap_remove_blob_8_1024,        remove_helper_v1,     Blob8, Blob1024;
    btreemap_remove_blob_8_1024_v2,     remove_helper_v2,     Blob8, Blob1024;
    btreemap_remove_blob_16_1024,       remove_helper_v1,    Blob16, Blob1024;
    btreemap_remove_blob_16_1024_v2,    remove_helper_v2,    Blob16, Blob1024;
    btreemap_remove_blob_32_1024,       remove_helper_v1,    Blob32, Blob1024;
    btreemap_remove_blob_32_1024_v2,    remove_helper_v2,    Blob32, Blob1024;
    btreemap_remove_blob_64_1024,       remove_helper_v1,    Blob64, Blob1024;
    btreemap_remove_blob_64_1024_v2,    remove_helper_v2,    Blob64, Blob1024;
    btreemap_remove_blob_128_1024,      remove_helper_v1,   Blob128, Blob1024;
    btreemap_remove_blob_128_1024_v2,   remove_helper_v2,   Blob128, Blob1024;
    btreemap_remove_blob_256_1024,      remove_helper_v1,   Blob256, Blob1024;
    btreemap_remove_blob_256_1024_v2,   remove_helper_v2,   Blob256, Blob1024;
    btreemap_remove_blob_512_1024,      remove_helper_v1,   Blob512, Blob1024;
    btreemap_remove_blob_512_1024_v2,   remove_helper_v2,   Blob512, Blob1024;

    btreemap_remove_u64_u64,            remove_helper_v1,   u64,     u64;
    btreemap_remove_u64_u64_v2,         remove_helper_v2,   u64,     u64;

    btreemap_remove_u64_blob_8,         remove_helper_v1,   u64,   Blob8;
    btreemap_remove_u64_blob_8_v2,      remove_helper_v2,   u64,   Blob8;
    btreemap_remove_blob_8_u64,         remove_helper_v1,   Blob8,   u64;
    btreemap_remove_blob_8_u64_v2,      remove_helper_v2,   Blob8,   u64;
}

// Benchmarks getting keys from a BTreeMap.
bench_tests! {
    // K x 1024
    btreemap_get_blob_4_1024,        get_helper_v1,     Blob4, Blob1024;
    btreemap_get_blob_4_1024_v2,     get_helper_v2,     Blob4, Blob1024;
    btreemap_get_blob_8_1024,        get_helper_v1,     Blob8, Blob1024;
    btreemap_get_blob_8_1024_v2,     get_helper_v2,     Blob8, Blob1024;
    btreemap_get_blob_16_1024,       get_helper_v1,    Blob16, Blob1024;
    btreemap_get_blob_16_1024_v2,    get_helper_v2,    Blob16, Blob1024;
    btreemap_get_blob_32_1024,       get_helper_v1,    Blob32, Blob1024;
    btreemap_get_blob_32_1024_v2,    get_helper_v2,    Blob32, Blob1024;
    btreemap_get_blob_64_1024,       get_helper_v1,    Blob64, Blob1024;
    btreemap_get_blob_64_1024_v2,    get_helper_v2,    Blob64, Blob1024;
    btreemap_get_blob_128_1024,      get_helper_v1,   Blob128, Blob1024;
    btreemap_get_blob_128_1024_v2,   get_helper_v2,   Blob128, Blob1024;
    btreemap_get_blob_256_1024,      get_helper_v1,   Blob256, Blob1024;
    btreemap_get_blob_256_1024_v2,   get_helper_v2,   Blob256, Blob1024;
    btreemap_get_blob_512_1024,      get_helper_v1,   Blob512, Blob1024;
    btreemap_get_blob_512_1024_v2,   get_helper_v2,   Blob512, Blob1024;
    btreemap_get_blob_512_1024_v2_mem_manager,  get_helper_v2_mem_manager,  Blob512, Blob1024;

    btreemap_get_u64_u64,            get_helper_v1,   u64,     u64;
    btreemap_get_u64_u64_v2,         get_helper_v2,   u64,     u64;
    btreemap_get_u64_u64_v2_mem_manager, get_helper_v2_mem_manager, u64, u64;

    btreemap_get_u64_blob_8,         get_helper_v1,   u64,   Blob8;
    btreemap_get_u64_blob_8_v2,      get_helper_v2,   u64,   Blob8;
    btreemap_get_blob_8_u64,         get_helper_v1,   Blob8,   u64;
    btreemap_get_blob_8_u64_v2,      get_helper_v2,   Blob8,   u64;
}

// Benchmarks `contains_key` of a BTreeMap.
bench_tests! {
    btreemap_contains_key_blob_4_1024,     contains_key_helper_v1,  Blob4, Blob1024;
    btreemap_contains_key_blob_4_1024_v2,  contains_key_helper_v2,  Blob4, Blob1024;
}

#[bench(raw)]
pub fn btreemap_insert_10mib_values() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());

    // Insert 20 10MiB values.
    let mut rng = Rng::from_seed(0);
    let mut values = vec![];
    for _ in 0..20 {
        values.push(
            rng.iter(Rand::rand_u8)
                .take(10 * 1024 * 1024)
                .collect::<Vec<_>>(),
        );
    }

    bench_fn(|| {
        for (i, value) in values.into_iter().enumerate() {
            btree.insert(i as u32, value);
        }
    })
}

// Read a range of entries but only process the key of each entry.
#[bench(raw)]
pub fn btreemap_read_keys_from_range() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let size: u32 = 10_000;
    for i in 0..size {
        btree.insert(i, vec![0; 1024]);
    }

    bench_fn(|| {
        btree
            .range((Bound::Included(0), Bound::Included(size)))
            .map(|entry| entry.0)
            .sum::<u32>()
    })
}

// Read a range of entries but only process the value from every third entry.
#[bench(raw)]
pub fn btreemap_read_every_third_value_from_range() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let size: u32 = 10_000;
    for i in 0..size {
        btree.insert(i, vec![0; 1024]);
    }

    bench_fn(|| {
        btree
            .range((Bound::Included(0), Bound::Included(size)))
            .filter(|entry| entry.0 % 3 == 0)
            .map(|entry| entry.1.len())
            .sum::<usize>()
    })
}

#[bench(raw)]
pub fn btreemap_iter_small_values() -> BenchResult {
    iter_helper(10_000, 0, IterType::Iter)
}

#[bench(raw)]
pub fn btreemap_iter_rev_small_values() -> BenchResult {
    iter_helper(10_000, 0, IterType::IterRev)
}

#[bench(raw)]
pub fn btreemap_iter_10mib_values() -> BenchResult {
    iter_helper(200, 10 * 1024, IterType::Iter)
}

#[bench(raw)]
pub fn btreemap_iter_rev_10mib_values() -> BenchResult {
    iter_helper(200, 10 * 1024, IterType::IterRev)
}

#[bench(raw)]
pub fn btreemap_keys_small_values() -> BenchResult {
    iter_helper(10_000, 0, IterType::Keys)
}

#[bench(raw)]
pub fn btreemap_keys_rev_small_values() -> BenchResult {
    iter_helper(10_000, 0, IterType::KeysRev)
}

#[bench(raw)]
pub fn btreemap_keys_10mib_values() -> BenchResult {
    iter_helper(200, 10 * 1024, IterType::Keys)
}

#[bench(raw)]
pub fn btreemap_keys_rev_10mib_values() -> BenchResult {
    iter_helper(200, 10 * 1024, IterType::KeysRev)
}

#[bench(raw)]
pub fn btreemap_values_small_values() -> BenchResult {
    iter_helper(10_000, 0, IterType::Values)
}

#[bench(raw)]
pub fn btreemap_values_rev_small_values() -> BenchResult {
    iter_helper(10_000, 0, IterType::ValuesRev)
}

#[bench(raw)]
pub fn btreemap_values_10mib_values() -> BenchResult {
    iter_helper(200, 10 * 1024, IterType::Values)
}

#[bench(raw)]
pub fn btreemap_values_rev_10mib_values() -> BenchResult {
    iter_helper(200, 10 * 1024, IterType::ValuesRev)
}

#[bench(raw)]
pub fn btreemap_iter_count_small_values() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let size: u32 = 10_000;
    for i in 0..size {
        btree.insert(i, vec![]);
    }

    bench_fn(|| {
        btree
            .range((Bound::Included(0), Bound::Included(size)))
            .count();
    })
}

#[bench(raw)]
pub fn btreemap_iter_count_10mib_values() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());

    let size: u8 = 200;

    // Insert 200 10MiB values.
    for i in 0..size {
        btree.insert(i, vec![0u8; 10 * 1024]);
    }

    bench_fn(|| {
        btree
            .range((Bound::Included(0), Bound::Included(size)))
            .count();
    })
}

#[bench(raw)]
pub fn btreemap_first_key_value() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let num_operations: u64 = 10_000;

    // Insert elements
    for i in 0..num_operations {
        btree.insert(i, vec![i as u8; 16]);
    }

    bench_fn(|| {
        // Access first_key_value multiple times
        for _ in 0..num_operations / 2 {
            btree.first_key_value();
        }
    })
}

#[bench(raw)]
pub fn btreemap_first_key_value_pop_first() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let num_operations: u64 = 10_000;

    // Insert elements
    for i in 0..num_operations {
        btree.insert(i, vec![i as u8; 16]);
    }

    bench_fn(|| {
        // Access first_key_value multiple times and pop first, hence first key value changes in each interation.
        for _ in 0..num_operations / 2 {
            btree.first_key_value();
            btree.pop_first();
        }
    })
}

#[bench(raw)]
pub fn btreemap_first_key_value_pop_last() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let num_operations: u64 = 10_000;

    // Insert elements
    for i in 0..num_operations {
        btree.insert(i, vec![i as u8; 16]);
    }

    bench_fn(|| {
        // Access first_key_value multiple times and pop last, hence first key value does not change.
        for _ in 0..num_operations / 2 {
            btree.first_key_value();
            btree.pop_last();
        }
    })
}

#[bench(raw)]
pub fn btreemap_last_key_value() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let num_operations: u64 = 10_000;

    // Insert elements
    for i in 0..num_operations {
        btree.insert(i, vec![i as u8; 16]);
    }

    bench_fn(|| {
        // Access last_key_value multiple times
        for _ in 0..num_operations {
            btree.last_key_value();
        }
    })
}

#[bench(raw)]
pub fn btreemap_last_key_value_pop_first() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let num_operations: u64 = 10_000;

    // Insert elements
    for i in 0..num_operations {
        btree.insert(i, vec![i as u8; 16]);
    }

    bench_fn(|| {
        // Access last_key_value multiple times and pop first, hence last key value does not chnage.
        for _ in 0..num_operations {
            btree.last_key_value();
            btree.pop_first();
        }
    })
}

#[bench(raw)]
pub fn btreemap_last_key_value_pop_last() -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let num_operations: u64 = 10_000;

    // Insert elements
    for i in 0..num_operations {
        btree.insert(i, vec![i as u8; 16]);
    }

    bench_fn(|| {
        // Access first_key_value multiple times and pop last, hence last key value changes in each interation.
        for _ in 0..num_operations {
            btree.last_key_value();
            btree.pop_last();
        }
    })
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_helper_v1<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<K, V>(btree)
}

fn insert_helper_v2<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<K, V>(btree)
}

fn insert_helper_v2_mem_manager<K: Clone + Ord + Storable + Random, V: Storable + Random>(
) -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    insert_helper::<K, V>(btree)
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, impl Memory>,
) -> BenchResult {
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let mut random_keys = Vec::with_capacity(num_keys);
    let mut random_values = Vec::with_capacity(num_keys);

    for _ in 0..num_keys {
        random_keys.push(K::random(&mut rng));
        random_values.push(V::random(&mut rng));
    }

    bench_fn(|| {
        // Insert the keys into the btree.
        for (k, v) in random_keys.into_iter().zip(random_values.into_iter()) {
            btree.insert(k, v);
        }
    })
}

// Profiles iterating over a btreemap.
fn iter_helper(size: u32, value_size: u32, iter_type: IterType) -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    for i in 0..size {
        btree.insert(i, vec![0u8; value_size as usize]);
    }

    match iter_type {
        IterType::Iter => bench_fn(|| for _ in btree.iter() {}),
        IterType::IterRev => bench_fn(|| for _ in btree.iter().rev() {}),
        IterType::Keys => bench_fn(|| for _ in btree.keys() {}),
        IterType::KeysRev => bench_fn(|| for _ in btree.keys().rev() {}),
        IterType::Values => bench_fn(|| for _ in btree.values() {}),
        IterType::ValuesRev => bench_fn(|| for _ in btree.values().rev() {}),
    }
}

// Profiles getting a large number of random blobs from a btreemap.
fn get_helper_v1<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<K, V>(btree)
}

fn get_helper_v2<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<K, V>(btree)
}

fn get_helper_v2_mem_manager<K: Clone + Ord + Storable + Random, V: Storable + Random>(
) -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    get_helper::<K, V>(btree)
}

fn get_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, impl Memory>,
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
    bench_fn(|| {
        for k in random_keys.into_iter() {
            btree.get(&k).unwrap();
        }
    })
}

// Profiles `contains_key` on a large number of random blobs from a btreemap.
fn contains_key_helper_v1<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult
{
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    contains_key_helper::<K, V>(btree)
}

fn contains_key_helper_v2<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult
{
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    contains_key_helper::<K, V>(btree)
}

fn contains_key_helper<K: Clone + Ord + Storable + Random, V: Storable + Random>(
    mut btree: BTreeMap<K, V, impl Memory>,
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

    // Checks if the keys are in the map.
    bench_fn(|| {
        for k in random_keys.into_iter() {
            btree.contains_key(&k);
        }
    })
}

// Inserts a large number of random blobs into a btreemap, then profiles removing them.
fn remove_helper_v1<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<K, V>(btree)
}

fn remove_helper_v2<K: Clone + Ord + Storable + Random, V: Storable + Random>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<K, V>(btree)
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

    bench_fn(|| {
        // Remove the keys from the btree.
        for k in random_keys.into_iter() {
            btree.remove(&k);
        }
    })
}

enum IterType {
    Iter,
    IterRev,
    Keys,
    KeysRev,
    Values,
    ValuesRev,
}
