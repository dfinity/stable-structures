use crate::Random;
use canbench_rs::{bench, bench_fn, BenchResult};
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
use ic_stable_structures::{
    storable::{Blob, FixedVec},
    BTreeMap, DefaultMemoryImpl, Memory, Storable,
};
use std::ops::Bound;
use tiny_rng::{Rand, Rng};

// Bounded types.
type Blob4 = Blob<4>;
type Blob8 = Blob<8>;
type Blob16 = Blob<16>;
type Blob32 = Blob<32>;
type Blob64 = Blob<64>;
type Blob128 = Blob<128>;
type Blob256 = Blob<256>;
type Blob512 = Blob<512>;
type Blob1024 = Blob<1024>;

// Unbounded types.
type FixedVec4 = FixedVec<4>;
type FixedVec8 = FixedVec<8>;
type FixedVec16 = FixedVec<16>;
type FixedVec32 = FixedVec<32>;
type FixedVec64 = FixedVec<64>;
type FixedVec128 = FixedVec<128>;
type FixedVec256 = FixedVec<256>;
type FixedVec512 = FixedVec<512>;
type FixedVec1024 = FixedVec<1024>;

trait TestKey: Clone + Ord + Storable + Random {}
impl<T> TestKey for T where T: Clone + Ord + Storable + Random {}

trait TestValue: Clone + Storable + Random {}
impl<T> TestValue for T where T: Clone + Storable + Random {}

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

fn generate_random_kv<K: TestKey, V: TestValue>(n: usize, rng: &mut Rng) -> Vec<(K, V)> {
    let mut pairs = Vec::with_capacity(n);
    for _ in 0..n {
        pairs.push((K::random(rng), V::random(rng)));
    }
    pairs
}

// Benchmarks for `BTreeMap::insert`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 1024
    btreemap_insert_blob_4_1024_v1,    insert_helper_v1,    Blob4, Blob1024;
    btreemap_insert_blob_8_1024_v1,    insert_helper_v1,    Blob8, Blob1024;
    btreemap_insert_blob_16_1024_v1,   insert_helper_v1,   Blob16, Blob1024;
    btreemap_insert_blob_32_1024_v1,   insert_helper_v1,   Blob32, Blob1024;
    btreemap_insert_blob_64_1024_v1,   insert_helper_v1,   Blob64, Blob1024;
    btreemap_insert_blob_128_1024_v1,  insert_helper_v1,  Blob128, Blob1024;
    btreemap_insert_blob_256_1024_v1,  insert_helper_v1,  Blob256, Blob1024;
    btreemap_insert_blob_512_1024_v1,  insert_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_insert_blob_1024_4_v1,    insert_helper_v1, Blob1024,    Blob4;
    btreemap_insert_blob_1024_8_v1,    insert_helper_v1, Blob1024,    Blob8;
    btreemap_insert_blob_1024_16_v1,   insert_helper_v1, Blob1024,   Blob16;
    btreemap_insert_blob_1024_32_v1,   insert_helper_v1, Blob1024,   Blob32;
    btreemap_insert_blob_1024_64_v1,   insert_helper_v1, Blob1024,   Blob64;
    btreemap_insert_blob_1024_128_v1,  insert_helper_v1, Blob1024,  Blob128;
    btreemap_insert_blob_1024_256_v1,  insert_helper_v1, Blob1024,  Blob256;
    btreemap_insert_blob_1024_512_v1,  insert_helper_v1, Blob1024,  Blob512;

    // V1 u64 / blob8
    btreemap_insert_u64_u64_v1,        insert_helper_v1, u64,     u64;
    btreemap_insert_u64_blob_8_v1,     insert_helper_v1, u64,   Blob8;
    btreemap_insert_blob_8_u64_v1,     insert_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 1024
    btreemap_insert_blob_4_1024_v2,    insert_helper_v2,    Blob4, Blob1024;
    btreemap_insert_blob_8_1024_v2,    insert_helper_v2,    Blob8, Blob1024;
    btreemap_insert_blob_16_1024_v2,   insert_helper_v2,   Blob16, Blob1024;
    btreemap_insert_blob_32_1024_v2,   insert_helper_v2,   Blob32, Blob1024;
    btreemap_insert_blob_64_1024_v2,   insert_helper_v2,   Blob64, Blob1024;
    btreemap_insert_blob_128_1024_v2,  insert_helper_v2,  Blob128, Blob1024;
    btreemap_insert_blob_256_1024_v2,  insert_helper_v2,  Blob256, Blob1024;
    btreemap_insert_blob_512_1024_v2,  insert_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_insert_blob_1024_4_v2,    insert_helper_v2, Blob1024,    Blob4;
    btreemap_insert_blob_1024_8_v2,    insert_helper_v2, Blob1024,    Blob8;
    btreemap_insert_blob_1024_16_v2,   insert_helper_v2, Blob1024,   Blob16;
    btreemap_insert_blob_1024_32_v2,   insert_helper_v2, Blob1024,   Blob32;
    btreemap_insert_blob_1024_64_v2,   insert_helper_v2, Blob1024,   Blob64;
    btreemap_insert_blob_1024_128_v2,  insert_helper_v2, Blob1024,  Blob128;
    btreemap_insert_blob_1024_256_v2,  insert_helper_v2, Blob1024,  Blob256;
    btreemap_insert_blob_1024_512_v2,  insert_helper_v2, Blob1024,  Blob512;

    // V2 vec K x 1024
    btreemap_insert_vec_4_1024_v2,    insert_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_insert_vec_8_1024_v2,    insert_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_insert_vec_16_1024_v2,   insert_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_insert_vec_32_1024_v2,   insert_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_insert_vec_64_1024_v2,   insert_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_insert_vec_128_1024_v2,  insert_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_insert_vec_256_1024_v2,  insert_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_insert_vec_512_1024_v2,  insert_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_insert_vec_1024_4_v2,    insert_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_insert_vec_1024_8_v2,    insert_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_insert_vec_1024_16_v2,   insert_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_insert_vec_1024_32_v2,   insert_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_insert_vec_1024_64_v2,   insert_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_insert_vec_1024_128_v2,  insert_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_insert_vec_1024_256_v2,  insert_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_insert_vec_1024_512_v2,  insert_helper_v2, FixedVec1024,  FixedVec512;

    // V2 u64 / blob8 / vec8
    btreemap_insert_u64_u64_v2,        insert_helper_v2,       u64,       u64;
    btreemap_insert_u64_blob_8_v2,     insert_helper_v2,       u64,     Blob8;
    btreemap_insert_blob_8_u64_v2,     insert_helper_v2,     Blob8,       u64;
    btreemap_insert_u64_vec_8_v2,      insert_helper_v2,       u64, FixedVec8;
    btreemap_insert_vec_8_u64_v2,      insert_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_insert_u64_u64_v2_mem_manager,      insert_helper_v2_mem_manager,         u64,         u64;
    btreemap_insert_u64_blob_512_v2_mem_manager, insert_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_insert_blob_512_u64_v2_mem_manager, insert_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_insert_u64_vec_512_v2_mem_manager,  insert_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_insert_vec_512_u64_v2_mem_manager,  insert_helper_v2_mem_manager, FixedVec512,         u64;
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_helper_v1<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<K, V>(btree)
}

fn insert_helper_v2<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<K, V>(btree)
}

fn insert_helper_v2_mem_manager<K: TestKey, V: TestValue>() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    insert_helper::<K, V>(btree)
}

// Profiles inserting a large number of random blobs into a btreemap.
fn insert_helper<K: TestKey, V: TestValue>(mut btree: BTreeMap<K, V, impl Memory>) -> BenchResult {
    let count = 10_000;
    let mut rng = Rng::from_seed(0);
    let items = generate_random_kv::<K, V>(count, &mut rng);

    bench_fn(|| {
        // Insert the items into the btree.
        for (k, v) in items {
            btree.insert(k, v);
        }
    })
}

// Benchmarks for `BTreeMap::remove`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 1024
    btreemap_remove_blob_4_1024_v1,    remove_helper_v1,    Blob4, Blob1024;
    btreemap_remove_blob_8_1024_v1,    remove_helper_v1,    Blob8, Blob1024;
    btreemap_remove_blob_16_1024_v1,   remove_helper_v1,   Blob16, Blob1024;
    btreemap_remove_blob_32_1024_v1,   remove_helper_v1,   Blob32, Blob1024;
    btreemap_remove_blob_64_1024_v1,   remove_helper_v1,   Blob64, Blob1024;
    btreemap_remove_blob_128_1024_v1,  remove_helper_v1,  Blob128, Blob1024;
    btreemap_remove_blob_256_1024_v1,  remove_helper_v1,  Blob256, Blob1024;
    btreemap_remove_blob_512_1024_v1,  remove_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_remove_blob_1024_4_v1,    remove_helper_v1, Blob1024,    Blob4;
    btreemap_remove_blob_1024_8_v1,    remove_helper_v1, Blob1024,    Blob8;
    btreemap_remove_blob_1024_16_v1,   remove_helper_v1, Blob1024,   Blob16;
    btreemap_remove_blob_1024_32_v1,   remove_helper_v1, Blob1024,   Blob32;
    btreemap_remove_blob_1024_64_v1,   remove_helper_v1, Blob1024,   Blob64;
    btreemap_remove_blob_1024_128_v1,  remove_helper_v1, Blob1024,  Blob128;
    btreemap_remove_blob_1024_256_v1,  remove_helper_v1, Blob1024,  Blob256;
    btreemap_remove_blob_1024_512_v1,  remove_helper_v1, Blob1024,  Blob512;

    // V1 u64 / blob8
    btreemap_remove_u64_u64_v1,        remove_helper_v1, u64,     u64;
    btreemap_remove_u64_blob_8_v1,     remove_helper_v1, u64,   Blob8;
    btreemap_remove_blob_8_u64_v1,     remove_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 1024
    btreemap_remove_blob_4_1024_v2,    remove_helper_v2,    Blob4, Blob1024;
    btreemap_remove_blob_8_1024_v2,    remove_helper_v2,    Blob8, Blob1024;
    btreemap_remove_blob_16_1024_v2,   remove_helper_v2,   Blob16, Blob1024;
    btreemap_remove_blob_32_1024_v2,   remove_helper_v2,   Blob32, Blob1024;
    btreemap_remove_blob_64_1024_v2,   remove_helper_v2,   Blob64, Blob1024;
    btreemap_remove_blob_128_1024_v2,  remove_helper_v2,  Blob128, Blob1024;
    btreemap_remove_blob_256_1024_v2,  remove_helper_v2,  Blob256, Blob1024;
    btreemap_remove_blob_512_1024_v2,  remove_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_remove_blob_1024_4_v2,    remove_helper_v2, Blob1024,    Blob4;
    btreemap_remove_blob_1024_8_v2,    remove_helper_v2, Blob1024,    Blob8;
    btreemap_remove_blob_1024_16_v2,   remove_helper_v2, Blob1024,   Blob16;
    btreemap_remove_blob_1024_32_v2,   remove_helper_v2, Blob1024,   Blob32;
    btreemap_remove_blob_1024_64_v2,   remove_helper_v2, Blob1024,   Blob64;
    btreemap_remove_blob_1024_128_v2,  remove_helper_v2, Blob1024,  Blob128;
    btreemap_remove_blob_1024_256_v2,  remove_helper_v2, Blob1024,  Blob256;
    btreemap_remove_blob_1024_512_v2,  remove_helper_v2, Blob1024,  Blob512;

    // V2 vec K x 1024
    btreemap_remove_vec_4_1024_v2,    remove_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_remove_vec_8_1024_v2,    remove_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_remove_vec_16_1024_v2,   remove_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_remove_vec_32_1024_v2,   remove_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_remove_vec_64_1024_v2,   remove_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_remove_vec_128_1024_v2,  remove_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_remove_vec_256_1024_v2,  remove_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_remove_vec_512_1024_v2,  remove_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_remove_vec_1024_4_v2,    remove_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_remove_vec_1024_8_v2,    remove_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_remove_vec_1024_16_v2,   remove_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_remove_vec_1024_32_v2,   remove_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_remove_vec_1024_64_v2,   remove_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_remove_vec_1024_128_v2,  remove_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_remove_vec_1024_256_v2,  remove_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_remove_vec_1024_512_v2,  remove_helper_v2, FixedVec1024,  FixedVec512;

    // V2 u64 / blob8 / vec8
    btreemap_remove_u64_u64_v2,        remove_helper_v2,       u64,       u64;
    btreemap_remove_u64_blob_8_v2,     remove_helper_v2,       u64,     Blob8;
    btreemap_remove_blob_8_u64_v2,     remove_helper_v2,     Blob8,       u64;
    btreemap_remove_u64_vec_8_v2,      remove_helper_v2,       u64, FixedVec8;
    btreemap_remove_vec_8_u64_v2,      remove_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_remove_u64_u64_v2_mem_manager,      remove_helper_v2_mem_manager,         u64,         u64;
    btreemap_remove_u64_blob_512_v2_mem_manager, remove_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_remove_blob_512_u64_v2_mem_manager, remove_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_remove_u64_vec_512_v2_mem_manager,  remove_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_remove_vec_512_u64_v2_mem_manager,  remove_helper_v2_mem_manager, FixedVec512,         u64;

}

// Inserts a large number of random blobs into a btreemap, then profiles removing them.
fn remove_helper_v1<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<K, V>(btree)
}

fn remove_helper_v2<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<K, V>(btree)
}

fn remove_helper_v2_mem_manager<K: TestKey, V: TestValue>() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    remove_helper::<K, V>(btree)
}

fn remove_helper<K: TestKey, V: TestValue>(mut btree: BTreeMap<K, V, impl Memory>) -> BenchResult {
    let count = 10_000;
    let mut rng = Rng::from_seed(0);
    let items = generate_random_kv::<K, V>(count, &mut rng);
    for (k, v) in items.clone() {
        btree.insert(k, v);
    }

    let keys: Vec<K> = items.into_iter().map(|(k, _)| k).collect();
    bench_fn(|| {
        // Remove the keys from the btree.
        for k in keys {
            btree.remove(&k);
        }
    })
}

// Benchmarks for `BTreeMap::get`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 1024
    btreemap_get_blob_4_1024_v1,    get_helper_v1,    Blob4, Blob1024;
    btreemap_get_blob_8_1024_v1,    get_helper_v1,    Blob8, Blob1024;
    btreemap_get_blob_16_1024_v1,   get_helper_v1,   Blob16, Blob1024;
    btreemap_get_blob_32_1024_v1,   get_helper_v1,   Blob32, Blob1024;
    btreemap_get_blob_64_1024_v1,   get_helper_v1,   Blob64, Blob1024;
    btreemap_get_blob_128_1024_v1,  get_helper_v1,  Blob128, Blob1024;
    btreemap_get_blob_256_1024_v1,  get_helper_v1,  Blob256, Blob1024;
    btreemap_get_blob_512_1024_v1,  get_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_get_blob_1024_4_v1,    get_helper_v1, Blob1024,    Blob4;
    btreemap_get_blob_1024_8_v1,    get_helper_v1, Blob1024,    Blob8;
    btreemap_get_blob_1024_16_v1,   get_helper_v1, Blob1024,   Blob16;
    btreemap_get_blob_1024_32_v1,   get_helper_v1, Blob1024,   Blob32;
    btreemap_get_blob_1024_64_v1,   get_helper_v1, Blob1024,   Blob64;
    btreemap_get_blob_1024_128_v1,  get_helper_v1, Blob1024,  Blob128;
    btreemap_get_blob_1024_256_v1,  get_helper_v1, Blob1024,  Blob256;
    btreemap_get_blob_1024_512_v1,  get_helper_v1, Blob1024,  Blob512;

    // V1 u64 / blob8
    btreemap_get_u64_u64_v1,        get_helper_v1, u64,     u64;
    btreemap_get_u64_blob_8_v1,     get_helper_v1, u64,   Blob8;
    btreemap_get_blob_8_u64_v1,     get_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 1024
    btreemap_get_blob_4_1024_v2,    get_helper_v2,    Blob4, Blob1024;
    btreemap_get_blob_8_1024_v2,    get_helper_v2,    Blob8, Blob1024;
    btreemap_get_blob_16_1024_v2,   get_helper_v2,   Blob16, Blob1024;
    btreemap_get_blob_32_1024_v2,   get_helper_v2,   Blob32, Blob1024;
    btreemap_get_blob_64_1024_v2,   get_helper_v2,   Blob64, Blob1024;
    btreemap_get_blob_128_1024_v2,  get_helper_v2,  Blob128, Blob1024;
    btreemap_get_blob_256_1024_v2,  get_helper_v2,  Blob256, Blob1024;
    btreemap_get_blob_512_1024_v2,  get_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_get_blob_1024_4_v2,    get_helper_v2, Blob1024,    Blob4;
    btreemap_get_blob_1024_8_v2,    get_helper_v2, Blob1024,    Blob8;
    btreemap_get_blob_1024_16_v2,   get_helper_v2, Blob1024,   Blob16;
    btreemap_get_blob_1024_32_v2,   get_helper_v2, Blob1024,   Blob32;
    btreemap_get_blob_1024_64_v2,   get_helper_v2, Blob1024,   Blob64;
    btreemap_get_blob_1024_128_v2,  get_helper_v2, Blob1024,  Blob128;
    btreemap_get_blob_1024_256_v2,  get_helper_v2, Blob1024,  Blob256;
    btreemap_get_blob_1024_512_v2,  get_helper_v2, Blob1024,  Blob512;

    // V2 vec K x 1024
    btreemap_get_vec_4_1024_v2,    get_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_get_vec_8_1024_v2,    get_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_get_vec_16_1024_v2,   get_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_get_vec_32_1024_v2,   get_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_get_vec_64_1024_v2,   get_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_get_vec_128_1024_v2,  get_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_get_vec_256_1024_v2,  get_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_get_vec_512_1024_v2,  get_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_get_vec_1024_4_v2,    get_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_get_vec_1024_8_v2,    get_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_get_vec_1024_16_v2,   get_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_get_vec_1024_32_v2,   get_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_get_vec_1024_64_v2,   get_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_get_vec_1024_128_v2,  get_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_get_vec_1024_256_v2,  get_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_get_vec_1024_512_v2,  get_helper_v2, FixedVec1024,  FixedVec512;

    // V2 u64 / blob8 / vec8
    btreemap_get_u64_u64_v2,        get_helper_v2,       u64,       u64;
    btreemap_get_u64_blob_8_v2,     get_helper_v2,       u64,     Blob8;
    btreemap_get_blob_8_u64_v2,     get_helper_v2,     Blob8,       u64;
    btreemap_get_u64_vec_8_v2,      get_helper_v2,       u64, FixedVec8;
    btreemap_get_vec_8_u64_v2,      get_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_get_u64_u64_v2_mem_manager,      get_helper_v2_mem_manager,         u64,         u64;
    btreemap_get_u64_blob_512_v2_mem_manager, get_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_get_blob_512_u64_v2_mem_manager, get_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_get_u64_vec_512_v2_mem_manager,  get_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_get_vec_512_u64_v2_mem_manager,  get_helper_v2_mem_manager, FixedVec512,         u64;
}

// Profiles getting a large number of random blobs from a btreemap.
fn get_helper_v1<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<K, V>(btree)
}

fn get_helper_v2<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<K, V>(btree)
}

fn get_helper_v2_mem_manager<K: TestKey, V: TestValue>() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    get_helper::<K, V>(btree)
}

fn get_helper<K: TestKey, V: TestValue>(mut btree: BTreeMap<K, V, impl Memory>) -> BenchResult {
    let count = 10_000;
    let mut rng = Rng::from_seed(0);
    let items = generate_random_kv::<K, V>(count, &mut rng);
    for (k, v) in items.clone() {
        btree.insert(k, v);
    }

    let keys: Vec<K> = items.into_iter().map(|(k, _)| k).collect();
    bench_fn(|| {
        // Get all the keys from the map.
        for k in keys {
            btree.get(&k).unwrap();
        }
    })
}

// Benchmarks for `BTreeMap::contains_key`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 1024
    btreemap_contains_blob_4_1024_v1,    contains_helper_v1,    Blob4, Blob1024;
    btreemap_contains_blob_8_1024_v1,    contains_helper_v1,    Blob8, Blob1024;
    btreemap_contains_blob_16_1024_v1,   contains_helper_v1,   Blob16, Blob1024;
    btreemap_contains_blob_32_1024_v1,   contains_helper_v1,   Blob32, Blob1024;
    btreemap_contains_blob_64_1024_v1,   contains_helper_v1,   Blob64, Blob1024;
    btreemap_contains_blob_128_1024_v1,  contains_helper_v1,  Blob128, Blob1024;
    btreemap_contains_blob_256_1024_v1,  contains_helper_v1,  Blob256, Blob1024;
    btreemap_contains_blob_512_1024_v1,  contains_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_contains_blob_1024_4_v1,    contains_helper_v1, Blob1024,    Blob4;
    btreemap_contains_blob_1024_8_v1,    contains_helper_v1, Blob1024,    Blob8;
    btreemap_contains_blob_1024_16_v1,   contains_helper_v1, Blob1024,   Blob16;
    btreemap_contains_blob_1024_32_v1,   contains_helper_v1, Blob1024,   Blob32;
    btreemap_contains_blob_1024_64_v1,   contains_helper_v1, Blob1024,   Blob64;
    btreemap_contains_blob_1024_128_v1,  contains_helper_v1, Blob1024,  Blob128;
    btreemap_contains_blob_1024_256_v1,  contains_helper_v1, Blob1024,  Blob256;
    btreemap_contains_blob_1024_512_v1,  contains_helper_v1, Blob1024,  Blob512;

    // V1 u64 / blob8
    btreemap_contains_u64_u64_v1,        contains_helper_v1, u64,     u64;
    btreemap_contains_u64_blob_8_v1,     contains_helper_v1, u64,   Blob8;
    btreemap_contains_blob_8_u64_v1,     contains_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 1024
    btreemap_contains_blob_4_1024_v2,    contains_helper_v2,    Blob4, Blob1024;
    btreemap_contains_blob_8_1024_v2,    contains_helper_v2,    Blob8, Blob1024;
    btreemap_contains_blob_16_1024_v2,   contains_helper_v2,   Blob16, Blob1024;
    btreemap_contains_blob_32_1024_v2,   contains_helper_v2,   Blob32, Blob1024;
    btreemap_contains_blob_64_1024_v2,   contains_helper_v2,   Blob64, Blob1024;
    btreemap_contains_blob_128_1024_v2,  contains_helper_v2,  Blob128, Blob1024;
    btreemap_contains_blob_256_1024_v2,  contains_helper_v2,  Blob256, Blob1024;
    btreemap_contains_blob_512_1024_v2,  contains_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_contains_blob_1024_4_v2,    contains_helper_v2, Blob1024,    Blob4;
    btreemap_contains_blob_1024_8_v2,    contains_helper_v2, Blob1024,    Blob8;
    btreemap_contains_blob_1024_16_v2,   contains_helper_v2, Blob1024,   Blob16;
    btreemap_contains_blob_1024_32_v2,   contains_helper_v2, Blob1024,   Blob32;
    btreemap_contains_blob_1024_64_v2,   contains_helper_v2, Blob1024,   Blob64;
    btreemap_contains_blob_1024_128_v2,  contains_helper_v2, Blob1024,  Blob128;
    btreemap_contains_blob_1024_256_v2,  contains_helper_v2, Blob1024,  Blob256;
    btreemap_contains_blob_1024_512_v2,  contains_helper_v2, Blob1024,  Blob512;

    // V2 vec K x 1024
    btreemap_contains_vec_4_1024_v2,    contains_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_contains_vec_8_1024_v2,    contains_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_contains_vec_16_1024_v2,   contains_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_contains_vec_32_1024_v2,   contains_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_contains_vec_64_1024_v2,   contains_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_contains_vec_128_1024_v2,  contains_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_contains_vec_256_1024_v2,  contains_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_contains_vec_512_1024_v2,  contains_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_contains_vec_1024_4_v2,    contains_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_contains_vec_1024_8_v2,    contains_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_contains_vec_1024_16_v2,   contains_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_contains_vec_1024_32_v2,   contains_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_contains_vec_1024_64_v2,   contains_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_contains_vec_1024_128_v2,  contains_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_contains_vec_1024_256_v2,  contains_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_contains_vec_1024_512_v2,  contains_helper_v2, FixedVec1024,  FixedVec512;

    // V2 u64 / blob8 / vec8
    btreemap_contains_u64_u64_v2,        contains_helper_v2,       u64,       u64;
    btreemap_contains_u64_blob_8_v2,     contains_helper_v2,       u64,     Blob8;
    btreemap_contains_blob_8_u64_v2,     contains_helper_v2,     Blob8,       u64;
    btreemap_contains_u64_vec_8_v2,      contains_helper_v2,       u64, FixedVec8;
    btreemap_contains_vec_8_u64_v2,      contains_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_contains_u64_u64_v2_mem_manager,      contains_helper_v2_mem_manager,         u64,         u64;
    btreemap_contains_u64_blob_512_v2_mem_manager, contains_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_contains_blob_512_u64_v2_mem_manager, contains_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_contains_u64_vec_512_v2_mem_manager,  contains_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_contains_vec_512_u64_v2_mem_manager,  contains_helper_v2_mem_manager, FixedVec512,         u64;
}

// Profiles `contains_key` on a large number of random blobs from a btreemap.
fn contains_helper_v1<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    contains_helper::<K, V>(btree)
}

fn contains_helper_v2<K: TestKey, V: TestValue>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    contains_helper::<K, V>(btree)
}

fn contains_helper_v2_mem_manager<K: TestKey, V: TestValue>() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    contains_helper::<K, V>(btree)
}

fn contains_helper<K: TestKey, V: TestValue>(
    mut btree: BTreeMap<K, V, impl Memory>,
) -> BenchResult {
    let count = 10_000;
    let mut rng = Rng::from_seed(0);
    let items = generate_random_kv::<K, V>(count, &mut rng);
    for (k, v) in items.clone() {
        btree.insert(k, v);
    }

    let keys: Vec<K> = items.into_iter().map(|(k, _)| k).collect();
    bench_fn(|| {
        // Checks if the keys are in the map.
        for k in keys {
            btree.contains_key(&k);
        }
    })
}

// #[bench(raw)]
// pub fn btreemap_insert_10mib_values() -> BenchResult {
//     let mut btree = BTreeMap::new(DefaultMemoryImpl::default());

//     // Insert 20 10MiB values.
//     let mut rng = Rng::from_seed(0);
//     let mut values = vec![];
//     for _ in 0..20 {
//         values.push(
//             rng.iter(Rand::rand_u8)
//                 .take(10 * 1024 * 1024)
//                 .collect::<Vec<_>>(),
//         );
//     }

//     bench_fn(|| {
//         for (i, value) in values.into_iter().enumerate() {
//             btree.insert(i as u32, value);
//         }
//     })
// }

// // Read a range of entries but only process the key of each entry.
// #[bench(raw)]
// pub fn btreemap_read_keys_from_range() -> BenchResult {
//     let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
//     let size: u32 = 10_000;
//     for i in 0..size {
//         btree.insert(i, vec![0; 1024]);
//     }

//     bench_fn(|| {
//         btree
//             .range((Bound::Included(0), Bound::Included(size)))
//             .map(|entry| entry.0)
//             .sum::<u32>()
//     })
// }

// // Read a range of entries but only process the value from every third entry.
// #[bench(raw)]
// pub fn btreemap_read_every_third_value_from_range() -> BenchResult {
//     let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
//     let size: u32 = 10_000;
//     for i in 0..size {
//         btree.insert(i, vec![0; 1024]);
//     }

//     bench_fn(|| {
//         btree
//             .range((Bound::Included(0), Bound::Included(size)))
//             .filter(|entry| entry.0 % 3 == 0)
//             .map(|entry| entry.1.len())
//             .sum::<usize>()
//     })
// }

// #[bench(raw)]
// pub fn btreemap_traverse_iter_small_values() -> BenchResult {
//     traversal_helper(10_000, 0, TraversalMode::Iter)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_iter_rev_small_values() -> BenchResult {
//     traversal_helper(10_000, 0, TraversalMode::IterRev)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_iter_10mib_values() -> BenchResult {
//     traversal_helper(200, 10 * 1024, TraversalMode::Iter)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_iter_rev_10mib_values() -> BenchResult {
//     traversal_helper(200, 10 * 1024, TraversalMode::IterRev)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_keys_small_values() -> BenchResult {
//     traversal_helper(10_000, 0, TraversalMode::Keys)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_keys_rev_small_values() -> BenchResult {
//     traversal_helper(10_000, 0, TraversalMode::KeysRev)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_keys_10mib_values() -> BenchResult {
//     traversal_helper(200, 10 * 1024, TraversalMode::Keys)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_keys_rev_10mib_values() -> BenchResult {
//     traversal_helper(200, 10 * 1024, TraversalMode::KeysRev)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_values_small_values() -> BenchResult {
//     traversal_helper(10_000, 0, TraversalMode::Values)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_values_rev_small_values() -> BenchResult {
//     traversal_helper(10_000, 0, TraversalMode::ValuesRev)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_values_10mib_values() -> BenchResult {
//     traversal_helper(200, 10 * 1024, TraversalMode::Values)
// }

// #[bench(raw)]
// pub fn btreemap_traverse_values_rev_10mib_values() -> BenchResult {
//     traversal_helper(200, 10 * 1024, TraversalMode::ValuesRev)
// }

// #[bench(raw)]
// pub fn btreemap_iter_count_small_values() -> BenchResult {
//     let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
//     let size: u32 = 10_000;
//     for i in 0..size {
//         btree.insert(i, vec![]);
//     }

//     bench_fn(|| {
//         btree
//             .range((Bound::Included(0), Bound::Included(size)))
//             .count();
//     })
// }

// #[bench(raw)]
// pub fn btreemap_iter_count_10mib_values() -> BenchResult {
//     let mut btree = BTreeMap::new(DefaultMemoryImpl::default());

//     let size: u8 = 200;

//     // Insert 200 10MiB values.
//     for i in 0..size {
//         btree.insert(i, vec![0u8; 10 * 1024]);
//     }

//     bench_fn(|| {
//         btree
//             .range((Bound::Included(0), Bound::Included(size)))
//             .count();
//     })
// }

// /// Benchmarks BTreeMap traversal for the given traversal mode.
// fn traversal_helper(size: u32, value_size: u32, traversal_mode: TraversalMode) -> BenchResult {
//     let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
//     for i in 0..size {
//         btree.insert(i, vec![0u8; value_size as usize]);
//     }

//     match traversal_mode {
//         TraversalMode::Iter => bench_fn(|| for _ in btree.iter() {}),
//         TraversalMode::IterRev => bench_fn(|| for _ in btree.iter().rev() {}),
//         TraversalMode::Keys => bench_fn(|| for _ in btree.keys() {}),
//         TraversalMode::KeysRev => bench_fn(|| for _ in btree.keys().rev() {}),
//         TraversalMode::Values => bench_fn(|| for _ in btree.values() {}),
//         TraversalMode::ValuesRev => bench_fn(|| for _ in btree.values().rev() {}),
//     }
// }

// enum TraversalMode {
//     Iter,
//     IterRev,
//     Keys,
//     KeysRev,
//     Values,
//     ValuesRev,
// }
