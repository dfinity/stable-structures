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

#[allow(non_upper_case_globals)]
const KiB: usize = 1024;
#[allow(non_upper_case_globals)]
const MiB: usize = 1024 * KiB;

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

fn generate_random_blocks(count: usize, block_size: usize, rng: &mut Rng) -> Vec<Vec<u8>> {
    (0..count)
        .map(|_| (0..block_size).map(|_| rng.rand_u8()).collect())
        .collect()
}

// Benchmarks for `BTreeMap::insert`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 32
    btreemap_v1_insert_blob_4_32,    insert_helper_v1,    Blob4, Blob32;
    btreemap_v1_insert_blob_8_32,    insert_helper_v1,    Blob8, Blob32;
    btreemap_v1_insert_blob_16_32,   insert_helper_v1,   Blob16, Blob32;
    btreemap_v1_insert_blob_32_32,   insert_helper_v1,   Blob32, Blob32;
    btreemap_v1_insert_blob_64_32,   insert_helper_v1,   Blob64, Blob32;
    btreemap_v1_insert_blob_128_32,  insert_helper_v1,  Blob128, Blob32;
    btreemap_v1_insert_blob_256_32,  insert_helper_v1,  Blob256, Blob32;
    btreemap_v1_insert_blob_512_32,  insert_helper_v1,  Blob512, Blob32;

    // V1 blob K x 1024
    btreemap_v1_insert_blob_4_1024,    insert_helper_v1,    Blob4, Blob1024;
    btreemap_v1_insert_blob_8_1024,    insert_helper_v1,    Blob8, Blob1024;
    btreemap_v1_insert_blob_16_1024,   insert_helper_v1,   Blob16, Blob1024;
    btreemap_v1_insert_blob_32_1024,   insert_helper_v1,   Blob32, Blob1024;
    btreemap_v1_insert_blob_64_1024,   insert_helper_v1,   Blob64, Blob1024;
    btreemap_v1_insert_blob_128_1024,  insert_helper_v1,  Blob128, Blob1024;
    btreemap_v1_insert_blob_256_1024,  insert_helper_v1,  Blob256, Blob1024;
    btreemap_v1_insert_blob_512_1024,  insert_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_v1_insert_blob_1024_4,    insert_helper_v1, Blob1024,    Blob4;
    btreemap_v1_insert_blob_1024_8,    insert_helper_v1, Blob1024,    Blob8;
    btreemap_v1_insert_blob_1024_16,   insert_helper_v1, Blob1024,   Blob16;
    btreemap_v1_insert_blob_1024_32,   insert_helper_v1, Blob1024,   Blob32;
    btreemap_v1_insert_blob_1024_64,   insert_helper_v1, Blob1024,   Blob64;
    btreemap_v1_insert_blob_1024_128,  insert_helper_v1, Blob1024,  Blob128;
    btreemap_v1_insert_blob_1024_256,  insert_helper_v1, Blob1024,  Blob256;
    btreemap_v1_insert_blob_1024_512,  insert_helper_v1, Blob1024,  Blob512;
    btreemap_v1_insert_blob_1024_1024, insert_helper_v1, Blob1024, Blob1024;

    // V1 u64 / blob8
    btreemap_v1_insert_u64_u64,        insert_helper_v1, u64,     u64;
    btreemap_v1_insert_u64_blob8,      insert_helper_v1, u64,   Blob8;
    btreemap_v1_insert_blob8_u64,      insert_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 32
    btreemap_v2_insert_blob_4_32,    insert_helper_v2,    Blob4, Blob32;
    btreemap_v2_insert_blob_8_32,    insert_helper_v2,    Blob8, Blob32;
    btreemap_v2_insert_blob_16_32,   insert_helper_v2,   Blob16, Blob32;
    btreemap_v2_insert_blob_32_32,   insert_helper_v2,   Blob32, Blob32;
    btreemap_v2_insert_blob_64_32,   insert_helper_v2,   Blob64, Blob32;
    btreemap_v2_insert_blob_128_32,  insert_helper_v2,  Blob128, Blob32;
    btreemap_v2_insert_blob_256_32,  insert_helper_v2,  Blob256, Blob32;
    btreemap_v2_insert_blob_512_32,  insert_helper_v2,  Blob512, Blob32;

    // V2 blob K x 1024
    btreemap_v2_insert_blob_4_1024,    insert_helper_v2,    Blob4, Blob1024;
    btreemap_v2_insert_blob_8_1024,    insert_helper_v2,    Blob8, Blob1024;
    btreemap_v2_insert_blob_16_1024,   insert_helper_v2,   Blob16, Blob1024;
    btreemap_v2_insert_blob_32_1024,   insert_helper_v2,   Blob32, Blob1024;
    btreemap_v2_insert_blob_64_1024,   insert_helper_v2,   Blob64, Blob1024;
    btreemap_v2_insert_blob_128_1024,  insert_helper_v2,  Blob128, Blob1024;
    btreemap_v2_insert_blob_256_1024,  insert_helper_v2,  Blob256, Blob1024;
    btreemap_v2_insert_blob_512_1024,  insert_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_v2_insert_blob_1024_4,    insert_helper_v2, Blob1024,    Blob4;
    btreemap_v2_insert_blob_1024_8,    insert_helper_v2, Blob1024,    Blob8;
    btreemap_v2_insert_blob_1024_16,   insert_helper_v2, Blob1024,   Blob16;
    btreemap_v2_insert_blob_1024_32,   insert_helper_v2, Blob1024,   Blob32;
    btreemap_v2_insert_blob_1024_64,   insert_helper_v2, Blob1024,   Blob64;
    btreemap_v2_insert_blob_1024_128,  insert_helper_v2, Blob1024,  Blob128;
    btreemap_v2_insert_blob_1024_256,  insert_helper_v2, Blob1024,  Blob256;
    btreemap_v2_insert_blob_1024_512,  insert_helper_v2, Blob1024,  Blob512;
    btreemap_v2_insert_blob_1024_1024,  insert_helper_v2, Blob1024,  Blob512;

    // V2 vec K x 32
    btreemap_v2_insert_vec_4_32,    insert_helper_v2,    FixedVec4, FixedVec32;
    btreemap_v2_insert_vec_8_32,    insert_helper_v2,    FixedVec8, FixedVec32;
    btreemap_v2_insert_vec_16_32,   insert_helper_v2,   FixedVec16, FixedVec32;
    btreemap_v2_insert_vec_32_32,   insert_helper_v2,   FixedVec32, FixedVec32;
    btreemap_v2_insert_vec_64_32,   insert_helper_v2,   FixedVec64, FixedVec32;
    btreemap_v2_insert_vec_128_32,  insert_helper_v2,  FixedVec128, FixedVec32;
    btreemap_v2_insert_vec_256_32,  insert_helper_v2,  FixedVec256, FixedVec32;
    btreemap_v2_insert_vec_512_32,  insert_helper_v2,  FixedVec512, FixedVec32;

    // V2 vec K x 1024
    btreemap_v2_insert_vec_4_1024,    insert_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_v2_insert_vec_8_1024,    insert_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_v2_insert_vec_16_1024,   insert_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_v2_insert_vec_32_1024,   insert_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_v2_insert_vec_64_1024,   insert_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_v2_insert_vec_128_1024,  insert_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_v2_insert_vec_256_1024,  insert_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_v2_insert_vec_512_1024,  insert_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_v2_insert_vec_1024_4,    insert_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_v2_insert_vec_1024_8,    insert_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_v2_insert_vec_1024_16,   insert_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_v2_insert_vec_1024_32,   insert_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_v2_insert_vec_1024_64,   insert_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_v2_insert_vec_1024_128,  insert_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_v2_insert_vec_1024_256,  insert_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_v2_insert_vec_1024_512,  insert_helper_v2, FixedVec1024,  FixedVec512;
    btreemap_v2_insert_vec_1024_1024, insert_helper_v2, FixedVec1024, FixedVec1024;

    // V2 u64 / blob8 / vec8
    btreemap_v2_insert_u64_u64,        insert_helper_v2,       u64,       u64;
    btreemap_v2_insert_u64_blob8,      insert_helper_v2,       u64,     Blob8;
    btreemap_v2_insert_blob8_u64,      insert_helper_v2,     Blob8,       u64;
    btreemap_v2_insert_u64_vec8,       insert_helper_v2,       u64, FixedVec8;
    btreemap_v2_insert_vec8_u64,       insert_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_v2_mem_manager_insert_u64_u64,      insert_helper_v2_mem_manager,         u64,         u64;
    btreemap_v2_mem_manager_insert_u64_blob512,  insert_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_v2_mem_manager_insert_blob512_u64,  insert_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_v2_mem_manager_insert_u64_vec512,   insert_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_v2_mem_manager_insert_vec512_u64,   insert_helper_v2_mem_manager, FixedVec512,         u64;
}

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

#[bench(raw)]
pub fn btreemap_v2_insert_10mib_values() -> BenchResult {
    let count = 20;
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let mut rng = Rng::from_seed(0);
    let values = generate_random_blocks(count, 10 * MiB, &mut rng);

    bench_fn(|| {
        for (i, value) in values.into_iter().enumerate() {
            btree.insert(i as u32, value);
        }
    })
}

// Benchmarks for `BTreeMap::remove`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 32
    btreemap_v1_remove_blob_4_32,    remove_helper_v1,    Blob4, Blob32;
    btreemap_v1_remove_blob_8_32,    remove_helper_v1,    Blob8, Blob32;
    btreemap_v1_remove_blob_16_32,   remove_helper_v1,   Blob16, Blob32;
    btreemap_v1_remove_blob_32_32,   remove_helper_v1,   Blob32, Blob32;
    btreemap_v1_remove_blob_64_32,   remove_helper_v1,   Blob64, Blob32;
    btreemap_v1_remove_blob_128_32,  remove_helper_v1,  Blob128, Blob32;
    btreemap_v1_remove_blob_256_32,  remove_helper_v1,  Blob256, Blob32;
    btreemap_v1_remove_blob_512_32,  remove_helper_v1,  Blob512, Blob32;

    // V1 blob K x 1024
    btreemap_v1_remove_blob_4_1024,    remove_helper_v1,    Blob4, Blob1024;
    btreemap_v1_remove_blob_8_1024,    remove_helper_v1,    Blob8, Blob1024;
    btreemap_v1_remove_blob_16_1024,   remove_helper_v1,   Blob16, Blob1024;
    btreemap_v1_remove_blob_32_1024,   remove_helper_v1,   Blob32, Blob1024;
    btreemap_v1_remove_blob_64_1024,   remove_helper_v1,   Blob64, Blob1024;
    btreemap_v1_remove_blob_128_1024,  remove_helper_v1,  Blob128, Blob1024;
    btreemap_v1_remove_blob_256_1024,  remove_helper_v1,  Blob256, Blob1024;
    btreemap_v1_remove_blob_512_1024,  remove_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_v1_remove_blob_1024_4,    remove_helper_v1, Blob1024,    Blob4;
    btreemap_v1_remove_blob_1024_8,    remove_helper_v1, Blob1024,    Blob8;
    btreemap_v1_remove_blob_1024_16,   remove_helper_v1, Blob1024,   Blob16;
    btreemap_v1_remove_blob_1024_32,   remove_helper_v1, Blob1024,   Blob32;
    btreemap_v1_remove_blob_1024_64,   remove_helper_v1, Blob1024,   Blob64;
    btreemap_v1_remove_blob_1024_128,  remove_helper_v1, Blob1024,  Blob128;
    btreemap_v1_remove_blob_1024_256,  remove_helper_v1, Blob1024,  Blob256;
    btreemap_v1_remove_blob_1024_512,  remove_helper_v1, Blob1024,  Blob512;
    btreemap_v1_remove_blob_1024_1024, remove_helper_v1, Blob1024, Blob1024;

    // V1 u64 / blob8
    btreemap_v1_remove_u64_u64,        remove_helper_v1, u64,     u64;
    btreemap_v1_remove_u64_blob8,      remove_helper_v1, u64,   Blob8;
    btreemap_v1_remove_blob8_u64,      remove_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 32
    btreemap_v2_remove_blob_4_32,    remove_helper_v2,    Blob4, Blob32;
    btreemap_v2_remove_blob_8_32,    remove_helper_v2,    Blob8, Blob32;
    btreemap_v2_remove_blob_16_32,   remove_helper_v2,   Blob16, Blob32;
    btreemap_v2_remove_blob_32_32,   remove_helper_v2,   Blob32, Blob32;
    btreemap_v2_remove_blob_64_32,   remove_helper_v2,   Blob64, Blob32;
    btreemap_v2_remove_blob_128_32,  remove_helper_v2,  Blob128, Blob32;
    btreemap_v2_remove_blob_256_32,  remove_helper_v2,  Blob256, Blob32;
    btreemap_v2_remove_blob_512_32,  remove_helper_v2,  Blob512, Blob32;

    // V2 blob K x 1024
    btreemap_v2_remove_blob_4_1024,    remove_helper_v2,    Blob4, Blob1024;
    btreemap_v2_remove_blob_8_1024,    remove_helper_v2,    Blob8, Blob1024;
    btreemap_v2_remove_blob_16_1024,   remove_helper_v2,   Blob16, Blob1024;
    btreemap_v2_remove_blob_32_1024,   remove_helper_v2,   Blob32, Blob1024;
    btreemap_v2_remove_blob_64_1024,   remove_helper_v2,   Blob64, Blob1024;
    btreemap_v2_remove_blob_128_1024,  remove_helper_v2,  Blob128, Blob1024;
    btreemap_v2_remove_blob_256_1024,  remove_helper_v2,  Blob256, Blob1024;
    btreemap_v2_remove_blob_512_1024,  remove_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_v2_remove_blob_1024_4,    remove_helper_v2, Blob1024,    Blob4;
    btreemap_v2_remove_blob_1024_8,    remove_helper_v2, Blob1024,    Blob8;
    btreemap_v2_remove_blob_1024_16,   remove_helper_v2, Blob1024,   Blob16;
    btreemap_v2_remove_blob_1024_32,   remove_helper_v2, Blob1024,   Blob32;
    btreemap_v2_remove_blob_1024_64,   remove_helper_v2, Blob1024,   Blob64;
    btreemap_v2_remove_blob_1024_128,  remove_helper_v2, Blob1024,  Blob128;
    btreemap_v2_remove_blob_1024_256,  remove_helper_v2, Blob1024,  Blob256;
    btreemap_v2_remove_blob_1024_512,  remove_helper_v2, Blob1024,  Blob512;
    btreemap_v2_remove_blob_1024_1024, remove_helper_v2, Blob1024, Blob1024;

    // V2 vec K x 32
    btreemap_v2_remove_vec_4_32,    remove_helper_v2,    FixedVec4, FixedVec32;
    btreemap_v2_remove_vec_8_32,    remove_helper_v2,    FixedVec8, FixedVec32;
    btreemap_v2_remove_vec_16_32,   remove_helper_v2,   FixedVec16, FixedVec32;
    btreemap_v2_remove_vec_32_32,   remove_helper_v2,   FixedVec32, FixedVec32;
    btreemap_v2_remove_vec_64_32,   remove_helper_v2,   FixedVec64, FixedVec32;
    btreemap_v2_remove_vec_128_32,  remove_helper_v2,  FixedVec128, FixedVec32;
    btreemap_v2_remove_vec_256_32,  remove_helper_v2,  FixedVec256, FixedVec32;
    btreemap_v2_remove_vec_512_32,  remove_helper_v2,  FixedVec512, FixedVec32;

    // V2 vec K x 1024
    btreemap_v2_remove_vec_4_1024,    remove_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_v2_remove_vec_8_1024,    remove_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_v2_remove_vec_16_1024,   remove_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_v2_remove_vec_32_1024,   remove_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_v2_remove_vec_64_1024,   remove_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_v2_remove_vec_128_1024,  remove_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_v2_remove_vec_256_1024,  remove_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_v2_remove_vec_512_1024,  remove_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_v2_remove_vec_1024_4,    remove_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_v2_remove_vec_1024_8,    remove_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_v2_remove_vec_1024_16,   remove_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_v2_remove_vec_1024_32,   remove_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_v2_remove_vec_1024_64,   remove_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_v2_remove_vec_1024_128,  remove_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_v2_remove_vec_1024_256,  remove_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_v2_remove_vec_1024_512,  remove_helper_v2, FixedVec1024,  FixedVec512;
    btreemap_v2_remove_vec_1024_1024, remove_helper_v2, FixedVec1024, FixedVec1024;

    // V2 u64 / blob8 / vec8
    btreemap_v2_remove_u64_u64,        remove_helper_v2,       u64,       u64;
    btreemap_v2_remove_u64_blob8,      remove_helper_v2,       u64,     Blob8;
    btreemap_v2_remove_blob8_u64,      remove_helper_v2,     Blob8,       u64;
    btreemap_v2_remove_u64_vec8,       remove_helper_v2,       u64, FixedVec8;
    btreemap_v2_remove_vec8_u64,       remove_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_v2_mem_manager_remove_u64_u64,      remove_helper_v2_mem_manager,         u64,         u64;
    btreemap_v2_mem_manager_remove_u64_blob512,  remove_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_v2_mem_manager_remove_blob512_u64,  remove_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_v2_mem_manager_remove_u64_vec512,   remove_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_v2_mem_manager_remove_vec512_u64,   remove_helper_v2_mem_manager, FixedVec512,         u64;
}

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

// Inserts a large number of random blobs into a btreemap, then profiles removing them.
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
        for random_key in keys {
            btree.remove(&random_key);
        }
    })
}

#[bench(raw)]
pub fn btreemap_v2_remove_10mib_values() -> BenchResult {
    let count = 20;
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let mut rng = Rng::from_seed(0);
    let values = generate_random_blocks(count, 10 * MiB, &mut rng);
    for (i, value) in values.into_iter().enumerate() {
        btree.insert(i as u32, value);
    }

    bench_fn(|| {
        for i in 0..count {
            btree.remove(&(i as u32));
        }
    })
}

// Benchmarks for `BTreeMap::get`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 32
    btreemap_v1_get_blob_4_32,    get_helper_v1,    Blob4, Blob32;
    btreemap_v1_get_blob_8_32,    get_helper_v1,    Blob8, Blob32;
    btreemap_v1_get_blob_16_32,   get_helper_v1,   Blob16, Blob32;
    btreemap_v1_get_blob_32_32,   get_helper_v1,   Blob32, Blob32;
    btreemap_v1_get_blob_64_32,   get_helper_v1,   Blob64, Blob32;
    btreemap_v1_get_blob_128_32,  get_helper_v1,  Blob128, Blob32;
    btreemap_v1_get_blob_256_32,  get_helper_v1,  Blob256, Blob32;
    btreemap_v1_get_blob_512_32,  get_helper_v1,  Blob512, Blob32;

    // V1 blob K x 1024
    btreemap_v1_get_blob_4_1024,    get_helper_v1,    Blob4, Blob1024;
    btreemap_v1_get_blob_8_1024,    get_helper_v1,    Blob8, Blob1024;
    btreemap_v1_get_blob_16_1024,   get_helper_v1,   Blob16, Blob1024;
    btreemap_v1_get_blob_32_1024,   get_helper_v1,   Blob32, Blob1024;
    btreemap_v1_get_blob_64_1024,   get_helper_v1,   Blob64, Blob1024;
    btreemap_v1_get_blob_128_1024,  get_helper_v1,  Blob128, Blob1024;
    btreemap_v1_get_blob_256_1024,  get_helper_v1,  Blob256, Blob1024;
    btreemap_v1_get_blob_512_1024,  get_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_v1_get_blob_1024_4,    get_helper_v1, Blob1024,    Blob4;
    btreemap_v1_get_blob_1024_8,    get_helper_v1, Blob1024,    Blob8;
    btreemap_v1_get_blob_1024_16,   get_helper_v1, Blob1024,   Blob16;
    btreemap_v1_get_blob_1024_32,   get_helper_v1, Blob1024,   Blob32;
    btreemap_v1_get_blob_1024_64,   get_helper_v1, Blob1024,   Blob64;
    btreemap_v1_get_blob_1024_128,  get_helper_v1, Blob1024,  Blob128;
    btreemap_v1_get_blob_1024_256,  get_helper_v1, Blob1024,  Blob256;
    btreemap_v1_get_blob_1024_512,  get_helper_v1, Blob1024,  Blob512;
    btreemap_v1_get_blob_1024_1024, get_helper_v1, Blob1024, Blob1024;

    // V1 u64 / blob8
    btreemap_v1_get_u64_u64,        get_helper_v1, u64,     u64;
    btreemap_v1_get_u64_blob8,      get_helper_v1, u64,   Blob8;
    btreemap_v1_get_blob8_u64,      get_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 32
    btreemap_v2_get_blob_4_32,    get_helper_v2,    Blob4, Blob32;
    btreemap_v2_get_blob_8_32,    get_helper_v2,    Blob8, Blob32;
    btreemap_v2_get_blob_16_32,   get_helper_v2,   Blob16, Blob32;
    btreemap_v2_get_blob_32_32,   get_helper_v2,   Blob32, Blob32;
    btreemap_v2_get_blob_64_32,   get_helper_v2,   Blob64, Blob32;
    btreemap_v2_get_blob_128_32,  get_helper_v2,  Blob128, Blob32;
    btreemap_v2_get_blob_256_32,  get_helper_v2,  Blob256, Blob32;
    btreemap_v2_get_blob_512_32,  get_helper_v2,  Blob512, Blob32;

    // V2 blob K x 1024
    btreemap_v2_get_blob_4_1024,    get_helper_v2,    Blob4, Blob1024;
    btreemap_v2_get_blob_8_1024,    get_helper_v2,    Blob8, Blob1024;
    btreemap_v2_get_blob_16_1024,   get_helper_v2,   Blob16, Blob1024;
    btreemap_v2_get_blob_32_1024,   get_helper_v2,   Blob32, Blob1024;
    btreemap_v2_get_blob_64_1024,   get_helper_v2,   Blob64, Blob1024;
    btreemap_v2_get_blob_128_1024,  get_helper_v2,  Blob128, Blob1024;
    btreemap_v2_get_blob_256_1024,  get_helper_v2,  Blob256, Blob1024;
    btreemap_v2_get_blob_512_1024,  get_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_v2_get_blob_1024_4,    get_helper_v2, Blob1024,    Blob4;
    btreemap_v2_get_blob_1024_8,    get_helper_v2, Blob1024,    Blob8;
    btreemap_v2_get_blob_1024_16,   get_helper_v2, Blob1024,   Blob16;
    btreemap_v2_get_blob_1024_32,   get_helper_v2, Blob1024,   Blob32;
    btreemap_v2_get_blob_1024_64,   get_helper_v2, Blob1024,   Blob64;
    btreemap_v2_get_blob_1024_128,  get_helper_v2, Blob1024,  Blob128;
    btreemap_v2_get_blob_1024_256,  get_helper_v2, Blob1024,  Blob256;
    btreemap_v2_get_blob_1024_512,  get_helper_v2, Blob1024,  Blob512;
    btreemap_v2_get_blob_1024_1024, get_helper_v2, Blob1024, Blob1024;

    // V2 vec K x 32
    btreemap_v2_get_vec_4_32,    get_helper_v2,    FixedVec4, FixedVec32;
    btreemap_v2_get_vec_8_32,    get_helper_v2,    FixedVec8, FixedVec32;
    btreemap_v2_get_vec_16_32,   get_helper_v2,   FixedVec16, FixedVec32;
    btreemap_v2_get_vec_32_32,   get_helper_v2,   FixedVec32, FixedVec32;
    btreemap_v2_get_vec_64_32,   get_helper_v2,   FixedVec64, FixedVec32;
    btreemap_v2_get_vec_128_32,  get_helper_v2,  FixedVec128, FixedVec32;
    btreemap_v2_get_vec_256_32,  get_helper_v2,  FixedVec256, FixedVec32;
    btreemap_v2_get_vec_512_32,  get_helper_v2,  FixedVec512, FixedVec32;

    // V2 vec K x 1024
    btreemap_v2_get_vec_4_1024,    get_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_v2_get_vec_8_1024,    get_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_v2_get_vec_16_1024,   get_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_v2_get_vec_32_1024,   get_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_v2_get_vec_64_1024,   get_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_v2_get_vec_128_1024,  get_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_v2_get_vec_256_1024,  get_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_v2_get_vec_512_1024,  get_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_v2_get_vec_1024_4,    get_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_v2_get_vec_1024_8,    get_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_v2_get_vec_1024_16,   get_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_v2_get_vec_1024_32,   get_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_v2_get_vec_1024_64,   get_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_v2_get_vec_1024_128,  get_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_v2_get_vec_1024_256,  get_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_v2_get_vec_1024_512,  get_helper_v2, FixedVec1024,  FixedVec512;
    btreemap_v2_get_vec_1024_1024, get_helper_v2, FixedVec1024, FixedVec1024;

    // V2 u64 / blob8 / vec8
    btreemap_v2_get_u64_u64,        get_helper_v2,       u64,       u64;
    btreemap_v2_get_u64_blob8,      get_helper_v2,       u64,     Blob8;
    btreemap_v2_get_blob8_u64,      get_helper_v2,     Blob8,       u64;
    btreemap_v2_get_u64_vec8,       get_helper_v2,       u64, FixedVec8;
    btreemap_v2_get_vec8_u64,       get_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_v2_mem_manager_get_u64_u64,      get_helper_v2_mem_manager,         u64,         u64;
    btreemap_v2_mem_manager_get_u64_blob512,  get_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_v2_mem_manager_get_blob512_u64,  get_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_v2_mem_manager_get_u64_vec512,   get_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_v2_mem_manager_get_vec512_u64,   get_helper_v2_mem_manager, FixedVec512,         u64;
}

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

// Profiles getting a large number of random blobs from a btreemap.
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
        for random_key in keys {
            btree.get(&random_key);
        }
    })
}

#[bench(raw)]
pub fn btreemap_v2_get_10mib_values() -> BenchResult {
    let count = 20;
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let mut rng = Rng::from_seed(0);
    let values = generate_random_blocks(count, 10 * MiB, &mut rng);
    for (i, value) in values.into_iter().enumerate() {
        btree.insert(i as u32, value);
    }

    bench_fn(|| {
        for i in 0..count {
            btree.get(&(i as u32));
        }
    })
}

// Benchmarks for `BTreeMap::contains_key`.
bench_tests! {
    // === V1 ===

    // V1 blob K x 32
    btreemap_v1_contains_blob_4_32,    contains_helper_v1,    Blob4, Blob32;
    btreemap_v1_contains_blob_8_32,    contains_helper_v1,    Blob8, Blob32;
    btreemap_v1_contains_blob_16_32,   contains_helper_v1,   Blob16, Blob32;
    btreemap_v1_contains_blob_32_32,   contains_helper_v1,   Blob32, Blob32;
    btreemap_v1_contains_blob_64_32,   contains_helper_v1,   Blob64, Blob32;
    btreemap_v1_contains_blob_128_32,  contains_helper_v1,  Blob128, Blob32;
    btreemap_v1_contains_blob_256_32,  contains_helper_v1,  Blob256, Blob32;
    btreemap_v1_contains_blob_512_32,  contains_helper_v1,  Blob512, Blob32;

    // V1 blob K x 1024
    btreemap_v1_contains_blob_4_1024,    contains_helper_v1,    Blob4, Blob1024;
    btreemap_v1_contains_blob_8_1024,    contains_helper_v1,    Blob8, Blob1024;
    btreemap_v1_contains_blob_16_1024,   contains_helper_v1,   Blob16, Blob1024;
    btreemap_v1_contains_blob_32_1024,   contains_helper_v1,   Blob32, Blob1024;
    btreemap_v1_contains_blob_64_1024,   contains_helper_v1,   Blob64, Blob1024;
    btreemap_v1_contains_blob_128_1024,  contains_helper_v1,  Blob128, Blob1024;
    btreemap_v1_contains_blob_256_1024,  contains_helper_v1,  Blob256, Blob1024;
    btreemap_v1_contains_blob_512_1024,  contains_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_v1_contains_blob_1024_4,    contains_helper_v1, Blob1024,    Blob4;
    btreemap_v1_contains_blob_1024_8,    contains_helper_v1, Blob1024,    Blob8;
    btreemap_v1_contains_blob_1024_16,   contains_helper_v1, Blob1024,   Blob16;
    btreemap_v1_contains_blob_1024_32,   contains_helper_v1, Blob1024,   Blob32;
    btreemap_v1_contains_blob_1024_64,   contains_helper_v1, Blob1024,   Blob64;
    btreemap_v1_contains_blob_1024_128,  contains_helper_v1, Blob1024,  Blob128;
    btreemap_v1_contains_blob_1024_256,  contains_helper_v1, Blob1024,  Blob256;
    btreemap_v1_contains_blob_1024_512,  contains_helper_v1, Blob1024,  Blob512;
    btreemap_v1_contains_blob_1024_1024, contains_helper_v1, Blob1024, Blob1024;

    // V1 u64 / blob8
    btreemap_v1_contains_u64_u64,        contains_helper_v1, u64,     u64;
    btreemap_v1_contains_u64_blob8,      contains_helper_v1, u64,   Blob8;
    btreemap_v1_contains_blob8_u64,      contains_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 32
    btreemap_v2_contains_blob_4_32,    contains_helper_v2,    Blob4, Blob32;
    btreemap_v2_contains_blob_8_32,    contains_helper_v2,    Blob8, Blob32;
    btreemap_v2_contains_blob_16_32,   contains_helper_v2,   Blob16, Blob32;
    btreemap_v2_contains_blob_32_32,   contains_helper_v2,   Blob32, Blob32;
    btreemap_v2_contains_blob_64_32,   contains_helper_v2,   Blob64, Blob32;
    btreemap_v2_contains_blob_128_32,  contains_helper_v2,  Blob128, Blob32;
    btreemap_v2_contains_blob_256_32,  contains_helper_v2,  Blob256, Blob32;
    btreemap_v2_contains_blob_512_32,  contains_helper_v2,  Blob512, Blob32;

    // V2 blob K x 1024
    btreemap_v2_contains_blob_4_1024,    contains_helper_v2,    Blob4, Blob1024;
    btreemap_v2_contains_blob_8_1024,    contains_helper_v2,    Blob8, Blob1024;
    btreemap_v2_contains_blob_16_1024,   contains_helper_v2,   Blob16, Blob1024;
    btreemap_v2_contains_blob_32_1024,   contains_helper_v2,   Blob32, Blob1024;
    btreemap_v2_contains_blob_64_1024,   contains_helper_v2,   Blob64, Blob1024;
    btreemap_v2_contains_blob_128_1024,  contains_helper_v2,  Blob128, Blob1024;
    btreemap_v2_contains_blob_256_1024,  contains_helper_v2,  Blob256, Blob1024;
    btreemap_v2_contains_blob_512_1024,  contains_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_v2_contains_blob_1024_4,    contains_helper_v2, Blob1024,    Blob4;
    btreemap_v2_contains_blob_1024_8,    contains_helper_v2, Blob1024,    Blob8;
    btreemap_v2_contains_blob_1024_16,   contains_helper_v2, Blob1024,   Blob16;
    btreemap_v2_contains_blob_1024_32,   contains_helper_v2, Blob1024,   Blob32;
    btreemap_v2_contains_blob_1024_64,   contains_helper_v2, Blob1024,   Blob64;
    btreemap_v2_contains_blob_1024_128,  contains_helper_v2, Blob1024,  Blob128;
    btreemap_v2_contains_blob_1024_256,  contains_helper_v2, Blob1024,  Blob256;
    btreemap_v2_contains_blob_1024_512,  contains_helper_v2, Blob1024,  Blob512;
    btreemap_v2_contains_blob_1024_1024, contains_helper_v2, Blob1024, Blob1024;

    // V2 vec K x 32
    btreemap_v2_contains_vec_4_32,    contains_helper_v2,    FixedVec4, FixedVec32;
    btreemap_v2_contains_vec_8_32,    contains_helper_v2,    FixedVec8, FixedVec32;
    btreemap_v2_contains_vec_16_32,   contains_helper_v2,   FixedVec16, FixedVec32;
    btreemap_v2_contains_vec_32_32,   contains_helper_v2,   FixedVec32, FixedVec32;
    btreemap_v2_contains_vec_64_32,   contains_helper_v2,   FixedVec64, FixedVec32;
    btreemap_v2_contains_vec_128_32,  contains_helper_v2,  FixedVec128, FixedVec32;
    btreemap_v2_contains_vec_256_32,  contains_helper_v2,  FixedVec256, FixedVec32;
    btreemap_v2_contains_vec_512_32,  contains_helper_v2,  FixedVec512, FixedVec32;

    // V2 vec K x 1024
    btreemap_v2_contains_vec_4_1024,    contains_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_v2_contains_vec_8_1024,    contains_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_v2_contains_vec_16_1024,   contains_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_v2_contains_vec_32_1024,   contains_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_v2_contains_vec_64_1024,   contains_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_v2_contains_vec_128_1024,  contains_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_v2_contains_vec_256_1024,  contains_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_v2_contains_vec_512_1024,  contains_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_v2_contains_vec_1024_4,    contains_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_v2_contains_vec_1024_8,    contains_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_v2_contains_vec_1024_16,   contains_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_v2_contains_vec_1024_32,   contains_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_v2_contains_vec_1024_64,   contains_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_v2_contains_vec_1024_128,  contains_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_v2_contains_vec_1024_256,  contains_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_v2_contains_vec_1024_512,  contains_helper_v2, FixedVec1024,  FixedVec512;
    btreemap_v2_contains_vec_1024_1024, contains_helper_v2, FixedVec1024, FixedVec1024;

    // V2 u64 / blob8 / vec8
    btreemap_v2_contains_u64_u64,        contains_helper_v2,       u64,       u64;
    btreemap_v2_contains_u64_blob8,      contains_helper_v2,       u64,     Blob8;
    btreemap_v2_contains_blob8_u64,      contains_helper_v2,     Blob8,       u64;
    btreemap_v2_contains_u64_vec8,       contains_helper_v2,       u64, FixedVec8;
    btreemap_v2_contains_vec8_u64,       contains_helper_v2, FixedVec8,       u64;

    // V2 memory manager u64 / blob512 / vec512
    btreemap_v2_mem_manager_contains_u64_u64,      contains_helper_v2_mem_manager,         u64,         u64;
    btreemap_v2_mem_manager_contains_u64_blob512,  contains_helper_v2_mem_manager,         u64,     Blob512;
    btreemap_v2_mem_manager_contains_blob512_u64,  contains_helper_v2_mem_manager,     Blob512,         u64;
    btreemap_v2_mem_manager_contains_u64_vec512,   contains_helper_v2_mem_manager,         u64, FixedVec512;
    btreemap_v2_mem_manager_contains_vec512_u64,   contains_helper_v2_mem_manager, FixedVec512,         u64;
}

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

// Profiles `contains_key` on a large number of random blobs from a btreemap.
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
        for random_key in keys {
            btree.contains_key(&random_key);
        }
    })
}

#[bench(raw)]
pub fn btreemap_v2_contains_10mib_values() -> BenchResult {
    let count = 20;
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let mut rng = Rng::from_seed(0);
    let values = generate_random_blocks(count, 10 * MiB, &mut rng);
    for (i, value) in values.into_iter().enumerate() {
        btree.insert(i as u32, value);
    }

    bench_fn(|| {
        for i in 0..count {
            btree.contains_key(&(i as u32));
        }
    })
}

/// Helper macro to generate traversal benchmarks.
macro_rules! bench_traversal_tests {
    (
        $(
            $fn_name:ident,
            $helper:ident,
            $count:expr,
            $value_size:expr,
            $traversal_mode:expr
        );+ $(;)?
    ) => {
        $(
            #[bench(raw)]
            pub fn $fn_name() -> BenchResult {
                $helper($count, $value_size, $traversal_mode)
            }
        )+
    };
}

bench_traversal_tests! {
    // === V1 ===
    // V1 does not support unbounded types, eg. Vec<_>.

    // === V2 ===
    // 1k items of 0 bytes
    btreemap_v2_scan_iter_1k_0b,        traverse_helper_v2, 1_000, 0, TraversalMode::Iter;
    btreemap_v2_scan_iter_rev_1k_0b,    traverse_helper_v2, 1_000, 0, TraversalMode::IterRev;
    btreemap_v2_scan_keys_1k_0b,        traverse_helper_v2, 1_000, 0, TraversalMode::Keys;
    btreemap_v2_scan_keys_rev_1k_0b,    traverse_helper_v2, 1_000, 0, TraversalMode::KeysRev;
    btreemap_v2_scan_values_1k_0b,      traverse_helper_v2, 1_000, 0, TraversalMode::Values;
    btreemap_v2_scan_values_rev_1k_0b,  traverse_helper_v2, 1_000, 0, TraversalMode::ValuesRev;

    // 1k items of 10 KiB
    btreemap_v2_scan_iter_1k_10kib,       traverse_helper_v2, 1_000, 10 * KiB, TraversalMode::Iter;
    btreemap_v2_scan_iter_rev_1k_10kib,   traverse_helper_v2, 1_000, 10 * KiB, TraversalMode::IterRev;
    btreemap_v2_scan_keys_1k_10kib,       traverse_helper_v2, 1_000, 10 * KiB, TraversalMode::Keys;
    btreemap_v2_scan_keys_rev_1k_10kib,   traverse_helper_v2, 1_000, 10 * KiB, TraversalMode::KeysRev;
    btreemap_v2_scan_values_1k_10kib,     traverse_helper_v2, 1_000, 10 * KiB, TraversalMode::Values;
    btreemap_v2_scan_values_rev_1k_10kib, traverse_helper_v2, 1_000, 10 * KiB, TraversalMode::ValuesRev;

    // 20 items of 10 MiB
    btreemap_v2_scan_iter_20_10mib,        traverse_helper_v2, 20, 10 * MiB, TraversalMode::Iter;
    btreemap_v2_scan_iter_rev_20_10mib,    traverse_helper_v2, 20, 10 * MiB, TraversalMode::IterRev;
    btreemap_v2_scan_keys_20_10mib,        traverse_helper_v2, 20, 10 * MiB, TraversalMode::Keys;
    btreemap_v2_scan_keys_rev_20_10mib,    traverse_helper_v2, 20, 10 * MiB, TraversalMode::KeysRev;
    btreemap_v2_scan_values_20_10mib,      traverse_helper_v2, 20, 10 * MiB, TraversalMode::Values;
    btreemap_v2_scan_values_rev_20_10mib,  traverse_helper_v2, 20, 10 * MiB, TraversalMode::ValuesRev;
}

enum TraversalMode {
    Iter,
    IterRev,
    Keys,
    KeysRev,
    Values,
    ValuesRev,
}

/// Benchmarks BTreeMap traversal for the given traversal mode.
fn traverse_helper_v2(count: u32, value_size: usize, traversal_mode: TraversalMode) -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    for i in 0..count {
        btree.insert(i, vec![0u8; value_size]);
    }

    match traversal_mode {
        TraversalMode::Iter => bench_fn(|| for _ in btree.iter() {}),
        TraversalMode::IterRev => bench_fn(|| for _ in btree.iter().rev() {}),
        TraversalMode::Keys => bench_fn(|| for _ in btree.keys() {}),
        TraversalMode::KeysRev => bench_fn(|| for _ in btree.keys().rev() {}),
        TraversalMode::Values => bench_fn(|| for _ in btree.values() {}),
        TraversalMode::ValuesRev => bench_fn(|| for _ in btree.values().rev() {}),
    }
}

/// Helper macro to generate range benchmarks.
macro_rules! bench_range_tests {
    ($( $fn_name:ident, $helper:ident, $count:expr, $size:expr );+ $(;)?) => {
        $(
            #[bench(raw)]
            pub fn $fn_name() -> BenchResult {
                $helper($count, $size)
            }
        )+
    };
}

bench_range_tests! {
    // === V1 ===
    // V1 does not support unbounded types, eg. Vec<_>.

    // === V2 ===
    btreemap_v2_range_key_sum_1k_0b,       range_key_sum_helper_v2, 1_000, 0;
    btreemap_v2_range_key_sum_1k_10kib,    range_key_sum_helper_v2, 1_000, 10 * KiB;
    btreemap_v2_range_key_sum_20_10mib,    range_key_sum_helper_v2, 20, 10 * MiB;

    btreemap_v2_range_value_sum_1k_0b,     range_value_sum_helper_v2, 1_000, 0;
    btreemap_v2_range_value_sum_1k_10kib,  range_value_sum_helper_v2, 1_000, 10 * KiB;
    btreemap_v2_range_value_sum_20_10mib,  range_value_sum_helper_v2, 20, 10 * MiB;

    btreemap_v2_range_count_1k_0b,         range_count_helper_v2, 1_000, 0;
    btreemap_v2_range_count_1k_10kib,      range_count_helper_v2, 1_000, 10 * KiB;
    btreemap_v2_range_count_20_10mib,      range_count_helper_v2, 20, 10 * MiB;
}

fn range_key_sum_helper_v2(count: usize, size: usize) -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let mut rng = Rng::from_seed(0);
    let values = generate_random_blocks(count, size, &mut rng);
    for (i, value) in values.into_iter().enumerate() {
        btree.insert(i as u32, value);
    }

    // Read a range of entries but only process the key of each entry.
    bench_fn(|| {
        btree
            .range((Bound::Included(0), Bound::Included(size as u32)))
            .map(|(k, _)| k)
            .sum::<u32>()
    })
}

fn range_value_sum_helper_v2(count: usize, size: usize) -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let mut rng = Rng::from_seed(0);
    let values = generate_random_blocks(count, size, &mut rng);
    for (i, value) in values.into_iter().enumerate() {
        btree.insert(i as u32, value);
    }

    // Read a range of entries but only process the value from every third entry.
    bench_fn(|| {
        btree
            .range((Bound::Included(0), Bound::Included(size as u32)))
            .filter(|(k, _)| k % 3 == 0)
            .map(|(_, v)| v.len())
            .sum::<usize>()
    })
}

fn range_count_helper_v2(count: usize, size: usize) -> BenchResult {
    let mut btree = BTreeMap::new(DefaultMemoryImpl::default());
    let mut rng = Rng::from_seed(0);
    let values = generate_random_blocks(count, size, &mut rng);
    for (i, value) in values.into_iter().enumerate() {
        btree.insert(i as u32, value);
    }

    bench_fn(|| {
        btree
            .range((Bound::Included(0), Bound::Included(size as u32)))
            .count()
    })
}

// First
bench_tests! {
    // === V1 ===

    // V1 blob K x 32
    btreemap_v1_pop_first_blob_4_32,    pop_first_helper_v1,    Blob4, Blob32;
    btreemap_v1_pop_first_blob_8_32,    pop_first_helper_v1,    Blob8, Blob32;
    btreemap_v1_pop_first_blob_16_32,   pop_first_helper_v1,   Blob16, Blob32;
    btreemap_v1_pop_first_blob_32_32,   pop_first_helper_v1,   Blob32, Blob32;
    btreemap_v1_pop_first_blob_64_32,   pop_first_helper_v1,   Blob64, Blob32;
    btreemap_v1_pop_first_blob_128_32,  pop_first_helper_v1,  Blob128, Blob32;
    btreemap_v1_pop_first_blob_256_32,  pop_first_helper_v1,  Blob256, Blob32;
    btreemap_v1_pop_first_blob_512_32,  pop_first_helper_v1,  Blob512, Blob32;

    // V1 blob K x 1024
    btreemap_v1_pop_first_blob_4_1024,    pop_first_helper_v1,    Blob4, Blob1024;
    btreemap_v1_pop_first_blob_8_1024,    pop_first_helper_v1,    Blob8, Blob1024;
    btreemap_v1_pop_first_blob_16_1024,   pop_first_helper_v1,   Blob16, Blob1024;
    btreemap_v1_pop_first_blob_32_1024,   pop_first_helper_v1,   Blob32, Blob1024;
    btreemap_v1_pop_first_blob_64_1024,   pop_first_helper_v1,   Blob64, Blob1024;
    btreemap_v1_pop_first_blob_128_1024,  pop_first_helper_v1,  Blob128, Blob1024;
    btreemap_v1_pop_first_blob_256_1024,  pop_first_helper_v1,  Blob256, Blob1024;
    btreemap_v1_pop_first_blob_512_1024,  pop_first_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_v1_pop_first_blob_1024_4,    pop_first_helper_v1, Blob1024,    Blob4;
    btreemap_v1_pop_first_blob_1024_8,    pop_first_helper_v1, Blob1024,    Blob8;
    btreemap_v1_pop_first_blob_1024_16,   pop_first_helper_v1, Blob1024,   Blob16;
    btreemap_v1_pop_first_blob_1024_32,   pop_first_helper_v1, Blob1024,   Blob32;
    btreemap_v1_pop_first_blob_1024_64,   pop_first_helper_v1, Blob1024,   Blob64;
    btreemap_v1_pop_first_blob_1024_128,  pop_first_helper_v1, Blob1024,  Blob128;
    btreemap_v1_pop_first_blob_1024_256,  pop_first_helper_v1, Blob1024,  Blob256;
    btreemap_v1_pop_first_blob_1024_512,  pop_first_helper_v1, Blob1024,  Blob512;
    btreemap_v1_pop_first_blob_1024_1024, pop_first_helper_v1, Blob1024, Blob1024;

    // V1 u64 / blob8
    btreemap_v1_pop_first_u64_u64,        pop_first_helper_v1, u64,     u64;
    btreemap_v1_pop_first_u64_blob8,      pop_first_helper_v1, u64,   Blob8;
    btreemap_v1_pop_first_blob8_u64,      pop_first_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 32
    btreemap_v2_pop_first_blob_4_32,    pop_first_helper_v2,    Blob4, Blob32;
    btreemap_v2_pop_first_blob_8_32,    pop_first_helper_v2,    Blob8, Blob32;
    btreemap_v2_pop_first_blob_16_32,   pop_first_helper_v2,   Blob16, Blob32;
    btreemap_v2_pop_first_blob_32_32,   pop_first_helper_v2,   Blob32, Blob32;
    btreemap_v2_pop_first_blob_64_32,   pop_first_helper_v2,   Blob64, Blob32;
    btreemap_v2_pop_first_blob_128_32,  pop_first_helper_v2,  Blob128, Blob32;
    btreemap_v2_pop_first_blob_256_32,  pop_first_helper_v2,  Blob256, Blob32;
    btreemap_v2_pop_first_blob_512_32,  pop_first_helper_v2,  Blob512, Blob32;

    // V2 blob K x 1024
    btreemap_v2_pop_first_blob_4_1024,    pop_first_helper_v2,    Blob4, Blob1024;
    btreemap_v2_pop_first_blob_8_1024,    pop_first_helper_v2,    Blob8, Blob1024;
    btreemap_v2_pop_first_blob_16_1024,   pop_first_helper_v2,   Blob16, Blob1024;
    btreemap_v2_pop_first_blob_32_1024,   pop_first_helper_v2,   Blob32, Blob1024;
    btreemap_v2_pop_first_blob_64_1024,   pop_first_helper_v2,   Blob64, Blob1024;
    btreemap_v2_pop_first_blob_128_1024,  pop_first_helper_v2,  Blob128, Blob1024;
    btreemap_v2_pop_first_blob_256_1024,  pop_first_helper_v2,  Blob256, Blob1024;
    btreemap_v2_pop_first_blob_512_1024,  pop_first_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_v2_pop_first_blob_1024_4,    pop_first_helper_v2, Blob1024,    Blob4;
    btreemap_v2_pop_first_blob_1024_8,    pop_first_helper_v2, Blob1024,    Blob8;
    btreemap_v2_pop_first_blob_1024_16,   pop_first_helper_v2, Blob1024,   Blob16;
    btreemap_v2_pop_first_blob_1024_32,   pop_first_helper_v2, Blob1024,   Blob32;
    btreemap_v2_pop_first_blob_1024_64,   pop_first_helper_v2, Blob1024,   Blob64;
    btreemap_v2_pop_first_blob_1024_128,  pop_first_helper_v2, Blob1024,  Blob128;
    btreemap_v2_pop_first_blob_1024_256,  pop_first_helper_v2, Blob1024,  Blob256;
    btreemap_v2_pop_first_blob_1024_512,  pop_first_helper_v2, Blob1024,  Blob512;
    btreemap_v2_pop_first_blob_1024_1024, pop_first_helper_v2, Blob1024, Blob1024;

    // V2 vec K x 32
    btreemap_v2_pop_first_vec_4_32,    pop_first_helper_v2,    FixedVec4, FixedVec32;
    btreemap_v2_pop_first_vec_8_32,    pop_first_helper_v2,    FixedVec8, FixedVec32;
    btreemap_v2_pop_first_vec_16_32,   pop_first_helper_v2,   FixedVec16, FixedVec32;
    btreemap_v2_pop_first_vec_32_32,   pop_first_helper_v2,   FixedVec32, FixedVec32;
    btreemap_v2_pop_first_vec_64_32,   pop_first_helper_v2,   FixedVec64, FixedVec32;
    btreemap_v2_pop_first_vec_128_32,  pop_first_helper_v2,  FixedVec128, FixedVec32;
    btreemap_v2_pop_first_vec_256_32,  pop_first_helper_v2,  FixedVec256, FixedVec32;
    btreemap_v2_pop_first_vec_512_32,  pop_first_helper_v2,  FixedVec512, FixedVec32;

    // V2 vec K x 1024
    btreemap_v2_pop_first_vec_4_1024,    pop_first_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_v2_pop_first_vec_8_1024,    pop_first_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_v2_pop_first_vec_16_1024,   pop_first_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_v2_pop_first_vec_32_1024,   pop_first_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_v2_pop_first_vec_64_1024,   pop_first_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_v2_pop_first_vec_128_1024,  pop_first_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_v2_pop_first_vec_256_1024,  pop_first_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_v2_pop_first_vec_512_1024,  pop_first_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_v2_pop_first_vec_1024_4,    pop_first_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_v2_pop_first_vec_1024_8,    pop_first_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_v2_pop_first_vec_1024_16,   pop_first_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_v2_pop_first_vec_1024_32,   pop_first_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_v2_pop_first_vec_1024_64,   pop_first_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_v2_pop_first_vec_1024_128,  pop_first_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_v2_pop_first_vec_1024_256,  pop_first_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_v2_pop_first_vec_1024_512,  pop_first_helper_v2, FixedVec1024,  FixedVec512;
    btreemap_v2_pop_first_vec_1024_1024, pop_first_helper_v2, FixedVec1024, FixedVec1024;

    // V2 u64 / blob8 / vec8
    btreemap_v2_pop_first_u64_u64,        pop_first_helper_v2,       u64,       u64;
    btreemap_v2_pop_first_u64_blob8,      pop_first_helper_v2,       u64,     Blob8;
    btreemap_v2_pop_first_blob8_u64,      pop_first_helper_v2,     Blob8,       u64;
    btreemap_v2_pop_first_u64_vec8,       pop_first_helper_v2,       u64, FixedVec8;
    btreemap_v2_pop_first_vec8_u64,       pop_first_helper_v2, FixedVec8,       u64;
}

// Last
bench_tests! {
    // === V1 ===

    // V1 blob K x 32
    btreemap_v1_pop_last_blob_4_32,    pop_last_helper_v1,    Blob4, Blob32;
    btreemap_v1_pop_last_blob_8_32,    pop_last_helper_v1,    Blob8, Blob32;
    btreemap_v1_pop_last_blob_16_32,   pop_last_helper_v1,   Blob16, Blob32;
    btreemap_v1_pop_last_blob_32_32,   pop_last_helper_v1,   Blob32, Blob32;
    btreemap_v1_pop_last_blob_64_32,   pop_last_helper_v1,   Blob64, Blob32;
    btreemap_v1_pop_last_blob_128_32,  pop_last_helper_v1,  Blob128, Blob32;
    btreemap_v1_pop_last_blob_256_32,  pop_last_helper_v1,  Blob256, Blob32;
    btreemap_v1_pop_last_blob_512_32,  pop_last_helper_v1,  Blob512, Blob32;

    // V1 blob K x 1024
    btreemap_v1_pop_last_blob_4_1024,    pop_last_helper_v1,    Blob4, Blob1024;
    btreemap_v1_pop_last_blob_8_1024,    pop_last_helper_v1,    Blob8, Blob1024;
    btreemap_v1_pop_last_blob_16_1024,   pop_last_helper_v1,   Blob16, Blob1024;
    btreemap_v1_pop_last_blob_32_1024,   pop_last_helper_v1,   Blob32, Blob1024;
    btreemap_v1_pop_last_blob_64_1024,   pop_last_helper_v1,   Blob64, Blob1024;
    btreemap_v1_pop_last_blob_128_1024,  pop_last_helper_v1,  Blob128, Blob1024;
    btreemap_v1_pop_last_blob_256_1024,  pop_last_helper_v1,  Blob256, Blob1024;
    btreemap_v1_pop_last_blob_512_1024,  pop_last_helper_v1,  Blob512, Blob1024;

    // V1 blob 1024 x V
    btreemap_v1_pop_last_blob_1024_4,    pop_last_helper_v1, Blob1024,    Blob4;
    btreemap_v1_pop_last_blob_1024_8,    pop_last_helper_v1, Blob1024,    Blob8;
    btreemap_v1_pop_last_blob_1024_16,   pop_last_helper_v1, Blob1024,   Blob16;
    btreemap_v1_pop_last_blob_1024_32,   pop_last_helper_v1, Blob1024,   Blob32;
    btreemap_v1_pop_last_blob_1024_64,   pop_last_helper_v1, Blob1024,   Blob64;
    btreemap_v1_pop_last_blob_1024_128,  pop_last_helper_v1, Blob1024,  Blob128;
    btreemap_v1_pop_last_blob_1024_256,  pop_last_helper_v1, Blob1024,  Blob256;
    btreemap_v1_pop_last_blob_1024_512,  pop_last_helper_v1, Blob1024,  Blob512;
    btreemap_v1_pop_last_blob_1024_1024, pop_last_helper_v1, Blob1024, Blob1024;

    // V1 u64 / blob8
    btreemap_v1_pop_last_u64_u64,        pop_last_helper_v1, u64,     u64;
    btreemap_v1_pop_last_u64_blob8,      pop_last_helper_v1, u64,   Blob8;
    btreemap_v1_pop_last_blob8_u64,      pop_last_helper_v1, Blob8,   u64;

    // === V2 ===

    // V2 blob K x 32
    btreemap_v2_pop_last_blob_4_32,    pop_last_helper_v2,    Blob4, Blob32;
    btreemap_v2_pop_last_blob_8_32,    pop_last_helper_v2,    Blob8, Blob32;
    btreemap_v2_pop_last_blob_16_32,   pop_last_helper_v2,   Blob16, Blob32;
    btreemap_v2_pop_last_blob_32_32,   pop_last_helper_v2,   Blob32, Blob32;
    btreemap_v2_pop_last_blob_64_32,   pop_last_helper_v2,   Blob64, Blob32;
    btreemap_v2_pop_last_blob_128_32,  pop_last_helper_v2,  Blob128, Blob32;
    btreemap_v2_pop_last_blob_256_32,  pop_last_helper_v2,  Blob256, Blob32;
    btreemap_v2_pop_last_blob_512_32,  pop_last_helper_v2,  Blob512, Blob32;

    // V2 blob K x 1024
    btreemap_v2_pop_last_blob_4_1024,    pop_last_helper_v2,    Blob4, Blob1024;
    btreemap_v2_pop_last_blob_8_1024,    pop_last_helper_v2,    Blob8, Blob1024;
    btreemap_v2_pop_last_blob_16_1024,   pop_last_helper_v2,   Blob16, Blob1024;
    btreemap_v2_pop_last_blob_32_1024,   pop_last_helper_v2,   Blob32, Blob1024;
    btreemap_v2_pop_last_blob_64_1024,   pop_last_helper_v2,   Blob64, Blob1024;
    btreemap_v2_pop_last_blob_128_1024,  pop_last_helper_v2,  Blob128, Blob1024;
    btreemap_v2_pop_last_blob_256_1024,  pop_last_helper_v2,  Blob256, Blob1024;
    btreemap_v2_pop_last_blob_512_1024,  pop_last_helper_v2,  Blob512, Blob1024;

    // V2 blob 1024 x V
    btreemap_v2_pop_last_blob_1024_4,    pop_last_helper_v2, Blob1024,    Blob4;
    btreemap_v2_pop_last_blob_1024_8,    pop_last_helper_v2, Blob1024,    Blob8;
    btreemap_v2_pop_last_blob_1024_16,   pop_last_helper_v2, Blob1024,   Blob16;
    btreemap_v2_pop_last_blob_1024_32,   pop_last_helper_v2, Blob1024,   Blob32;
    btreemap_v2_pop_last_blob_1024_64,   pop_last_helper_v2, Blob1024,   Blob64;
    btreemap_v2_pop_last_blob_1024_128,  pop_last_helper_v2, Blob1024,  Blob128;
    btreemap_v2_pop_last_blob_1024_256,  pop_last_helper_v2, Blob1024,  Blob256;
    btreemap_v2_pop_last_blob_1024_512,  pop_last_helper_v2, Blob1024,  Blob512;
    btreemap_v2_pop_last_blob_1024_1024, pop_last_helper_v2, Blob1024, Blob1024;

    // V2 vec K x 32
    btreemap_v2_pop_last_vec_4_32,    pop_last_helper_v2,    FixedVec4, FixedVec32;
    btreemap_v2_pop_last_vec_8_32,    pop_last_helper_v2,    FixedVec8, FixedVec32;
    btreemap_v2_pop_last_vec_16_32,   pop_last_helper_v2,   FixedVec16, FixedVec32;
    btreemap_v2_pop_last_vec_32_32,   pop_last_helper_v2,   FixedVec32, FixedVec32;
    btreemap_v2_pop_last_vec_64_32,   pop_last_helper_v2,   FixedVec64, FixedVec32;
    btreemap_v2_pop_last_vec_128_32,  pop_last_helper_v2,  FixedVec128, FixedVec32;
    btreemap_v2_pop_last_vec_256_32,  pop_last_helper_v2,  FixedVec256, FixedVec32;
    btreemap_v2_pop_last_vec_512_32,  pop_last_helper_v2,  FixedVec512, FixedVec32;

    // V2 vec K x 1024
    btreemap_v2_pop_last_vec_4_1024,    pop_last_helper_v2,    FixedVec4, FixedVec1024;
    btreemap_v2_pop_last_vec_8_1024,    pop_last_helper_v2,    FixedVec8, FixedVec1024;
    btreemap_v2_pop_last_vec_16_1024,   pop_last_helper_v2,   FixedVec16, FixedVec1024;
    btreemap_v2_pop_last_vec_32_1024,   pop_last_helper_v2,   FixedVec32, FixedVec1024;
    btreemap_v2_pop_last_vec_64_1024,   pop_last_helper_v2,   FixedVec64, FixedVec1024;
    btreemap_v2_pop_last_vec_128_1024,  pop_last_helper_v2,  FixedVec128, FixedVec1024;
    btreemap_v2_pop_last_vec_256_1024,  pop_last_helper_v2,  FixedVec256, FixedVec1024;
    btreemap_v2_pop_last_vec_512_1024,  pop_last_helper_v2,  FixedVec512, FixedVec1024;

    // V2 vec 1024 x V
    btreemap_v2_pop_last_vec_1024_4,    pop_last_helper_v2, FixedVec1024,    FixedVec4;
    btreemap_v2_pop_last_vec_1024_8,    pop_last_helper_v2, FixedVec1024,    FixedVec8;
    btreemap_v2_pop_last_vec_1024_16,   pop_last_helper_v2, FixedVec1024,   FixedVec16;
    btreemap_v2_pop_last_vec_1024_32,   pop_last_helper_v2, FixedVec1024,   FixedVec32;
    btreemap_v2_pop_last_vec_1024_64,   pop_last_helper_v2, FixedVec1024,   FixedVec64;
    btreemap_v2_pop_last_vec_1024_128,  pop_last_helper_v2, FixedVec1024,  FixedVec128;
    btreemap_v2_pop_last_vec_1024_256,  pop_last_helper_v2, FixedVec1024,  FixedVec256;
    btreemap_v2_pop_last_vec_1024_512,  pop_last_helper_v2, FixedVec1024,  FixedVec512;
    btreemap_v2_pop_last_vec_1024_1024, pop_last_helper_v2, FixedVec1024, FixedVec1024;

    // V2 u64 / blob8 / vec8
    btreemap_v2_pop_last_u64_u64,        pop_last_helper_v2,       u64,       u64;
    btreemap_v2_pop_last_u64_blob8,      pop_last_helper_v2,       u64,     Blob8;
    btreemap_v2_pop_last_blob8_u64,      pop_last_helper_v2,     Blob8,       u64;
    btreemap_v2_pop_last_u64_vec8,       pop_last_helper_v2,       u64, FixedVec8;
    btreemap_v2_pop_last_vec8_u64,       pop_last_helper_v2, FixedVec8,       u64;
}

fn pop_first_helper_v1<K: TestKey, V: TestValue>() -> BenchResult {
    pop_helper_v1::<K, V>(Position::First)
}

fn pop_last_helper_v1<K: TestKey, V: TestValue>() -> BenchResult {
    pop_helper_v1::<K, V>(Position::Last)
}

fn pop_first_helper_v2<K: TestKey, V: TestValue>() -> BenchResult {
    pop_helper_v2::<K, V>(Position::First)
}

fn pop_last_helper_v2<K: TestKey, V: TestValue>() -> BenchResult {
    pop_helper_v2::<K, V>(Position::Last)
}

fn pop_helper_v1<K: TestKey, V: TestValue>(position: Position) -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    pop_helper::<K, V>(btree, position)
}

fn pop_helper_v2<K: TestKey, V: TestValue>(position: Position) -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    pop_helper::<K, V>(btree, position)
}

enum Position {
    First,
    Last,
}

fn pop_helper<K: TestKey, V: TestValue>(
    mut btree: BTreeMap<K, V, impl Memory>,
    position: Position,
) -> BenchResult {
    let count = 10_000;
    let mut rng = Rng::from_seed(0);
    let items = generate_random_kv::<K, V>(count, &mut rng);
    for (k, v) in items {
        btree.insert(k, v);
    }

    bench_fn(|| {
        for _ in 0..count {
            match position {
                Position::First => btree.pop_first(),
                Position::Last => btree.pop_last(),
            };
        }
    })
}
