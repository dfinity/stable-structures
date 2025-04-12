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

// canbench btreemap_first_entry

type Vec1024 = Vec<u8>;
type String1024 = String;

type Key = String1024;
type Value = String1024;
type Entry = (Key, Value);

// Generates an array of N bytes, placing the u32's big-endian bytes at the end (slowest cmp).
fn make_buffer<const N: usize>(i: u32) -> [u8; N] {
    let mut buf = [0u8; N];
    let bytes = i.to_be_bytes();
    buf[N - bytes.len()..].copy_from_slice(&bytes);
    buf
}

trait Make<T> {
    fn make(_i: u32) -> T {
        panic!("not implemented for {:?}", std::any::type_name::<T>())
    }
}

impl Make<u32> for u32 {
    fn make(i: u32) -> Self {
        i
    }
}

impl Make<u64> for u64 {
    fn make(i: u32) -> Self {
        i as u64
    }
}

impl<const N: usize> Make<Blob<N>> for Blob<N> {
    fn make(i: u32) -> Self {
        Blob::try_from(&make_buffer::<N>(i)[..]).unwrap()
    }
}

impl Make<Vec1024> for Vec1024 {
    fn make(i: u32) -> Self {
        make_buffer::<1024>(i).to_vec()
    }
}

impl Make<String1024> for String1024 {
    fn make(i: u32) -> Self {
        // "000...{i}" forces comparisons to check all 1024 characters (slowest cmp).
        format!("{:0>1024}", i)
    }
}

trait MakeRandom<T: Make<T>> {
    fn make_random(rng: &mut Rng) -> T {
        let i = Rand::rand_u32(rng);
        T::make(i)
    }
}

impl MakeRandom<u32> for u32 {}
impl MakeRandom<u64> for u64 {}
impl<const N: usize> MakeRandom<Blob<N>> for Blob<N> {}
impl MakeRandom<Vec1024> for Vec1024 {}
impl MakeRandom<String1024> for String1024 {}

fn generate_entries(count: usize) -> Vec<Entry> {
    (0..count)
        .map(|i| (Key::make(i as u32), Value::make(1_000 * i as u32)))
        .collect::<Vec<_>>()
}

#[bench(raw)]
pub fn btreemap_first_entry_insert() -> BenchResult {
    let num_keys = 10_000;
    let entries = generate_entries(num_keys);

    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    bench_fn(|| {
        // Iterate in reverse order to trigger cached key comparisons.
        for (k, v) in entries.into_iter().rev() {
            btree.insert(k, v);
            if btree.len() == 1 {
                btree.first_key_value();
                btree.last_key_value();
            }
        }
    })
}

#[bench(raw)]
pub fn btreemap_first_entry_remove() -> BenchResult {
    let num_keys = 10_000;
    let entries = generate_entries(num_keys);

    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    for (k, v) in entries.clone().into_iter() {
        assert_eq!(btree.insert(k, v), None);
    }

    // Populate the cache to trigger cached key comparisons.
    btree.first_key_value();
    btree.last_key_value();
    bench_fn(|| {
        // Iterate in ascending order to trigger cached key comparisons.
        for (k, _) in entries.into_iter() {
            btree.remove(&k);
        }
    })
}

#[bench(raw)]
pub fn btreemap_first_entry_read() -> BenchResult {
    let num_keys = 10_000;
    let entries = generate_entries(num_keys);

    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    for (k, v) in entries.clone().into_iter() {
        assert_eq!(btree.insert(k, v), None);
    }

    bench_fn(|| {
        for _ in 0..num_keys {
            btree.first_key_value();
        }
    })
}

#[bench(raw)]
pub fn btreemap_first_entry_pop() -> BenchResult {
    let num_keys = 10_000;
    let entries = generate_entries(num_keys);

    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    for (k, v) in entries.clone().into_iter() {
        assert_eq!(btree.insert(k, v), None);
    }

    bench_fn(|| {
        // Iterate in ascending order to trigger cached key comparisons.
        for _ in 0..num_keys {
            btree.pop_first();
        }
    })
}

#[bench(raw)]
pub fn btreemap_first_entry_mixed_workload() -> BenchResult {
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let entries: Vec<_> = (0..num_keys)
        .map(|_| (Key::make_random(&mut rng), Value::make_random(&mut rng)))
        .collect();
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    for (k, v) in entries.clone() {
        btree.insert(k, v);
    }
    // Precompute operations.
    enum Op {
        Insert(Key, Value),
        Remove(Key),
        Read,
    }
    let ops: Vec<Op> = (0..5_000)
        .map(|i| match i % 5 {
            0 => Op::Insert(Key::make_random(&mut rng), Value::make_random(&mut rng)),
            1 => Op::Remove(entries[i as usize % num_keys].0.clone()),
            _ => Op::Read,
        })
        .collect();
    bench_fn(|| {
        for op in &ops {
            match op {
                Op::Insert(key, value) => {
                    btree.insert(key.clone(), value.clone());
                }
                Op::Remove(key) => {
                    btree.remove(key);
                }
                Op::Read => {
                    btree.first_key_value();
                }
            }
        }
    })
}

#[bench(raw)]
pub fn btreemap_first_entry_priority_queue() -> BenchResult {
    let num_keys = 10_000;
    let mut rng = Rng::from_seed(0);
    let entries: Vec<_> = (0..num_keys)
        .map(|_| (Key::make_random(&mut rng), Value::make_random(&mut rng)))
        .collect();
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    for (k, v) in entries.clone() {
        btree.insert(k, v);
    }
    // Precompute keys and values for insertions.
    let inserts: Vec<(Key, Value)> = (0..5_000)
        .map(|_| (Key::make_random(&mut rng), Value::make_random(&mut rng)))
        .collect();
    bench_fn(|| {
        for (key, value) in &inserts {
            btree.pop_first();
            btree.insert(key.clone(), value.clone());
        }
    })
}
