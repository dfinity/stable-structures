use crate::Random;
use canbench_rs::{bench, bench_fn, BenchResult};
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
use ic_stable_structures::{storable::Blob, BTreeMap, DefaultMemoryImpl, Memory, Storable};
use std::ops::Bound;
use tiny_rng::{Rand, Rng};

/// Helper macro to generate benchmarks.
macro_rules! bench_tests {
    ($( $fn_name:ident, $helper:ident, $value:expr, $size:expr );+ $(;)?) => {
        $(
            #[bench(raw)]
            pub fn $fn_name() -> BenchResult {
                $helper::<$value, $size>()
            }
        )+
    };
}

// Benchmarks inserting blobs into a BTreeMap.
bench_tests! {
    // x1024
    btreemap_insert_blob_4_1024,    insert_blob_helper,          4, 1024;
    btreemap_insert_blob_4_1024_v2, insert_blob_helper_v2,       4, 1024;
    btreemap_insert_blob_8_1024,    insert_blob_helper,          8, 1024;
    btreemap_insert_blob_8_1024_v2, insert_blob_helper_v2,       8, 1024;
    btreemap_insert_blob_16_1024,    insert_blob_helper,        16, 1024;
    btreemap_insert_blob_16_1024_v2, insert_blob_helper_v2,     16, 1024;
    btreemap_insert_blob_32_1024,    insert_blob_helper,        32, 1024;
    btreemap_insert_blob_32_1024_v2, insert_blob_helper_v2,     32, 1024;
    btreemap_insert_blob_64_1024,    insert_blob_helper,        64, 1024;
    btreemap_insert_blob_64_1024_v2, insert_blob_helper_v2,     64, 1024;
    btreemap_insert_blob_128_1024,    insert_blob_helper,      128, 1024;
    btreemap_insert_blob_128_1024_v2, insert_blob_helper_v2,   128, 1024;
    btreemap_insert_blob_256_1024,    insert_blob_helper,      256, 1024;
    btreemap_insert_blob_256_1024_v2, insert_blob_helper_v2,   256, 1024;
    btreemap_insert_blob_512_1024,    insert_blob_helper,      512, 1024;
    btreemap_insert_blob_512_1024_v2, insert_blob_helper_v2,   512, 1024;
    btreemap_insert_blob_1024_1024,    insert_blob_helper,    1024, 1024;
    btreemap_insert_blob_1024_1024_v2, insert_blob_helper_v2, 1024, 1024;
    btreemap_insert_blob_1024_1024_v2_mem_manager, insert_blob_helper_v2_mem_manager, 1024, 1024;
}

#[bench(raw)]
pub fn btreemap_insert_u64_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<u64, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_insert_u64_u64_mem_manager() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    insert_helper::<u64, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_insert_u64_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<u64, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_insert_u64_blob_8() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<u64, Blob<8>>(btree)
}

#[bench(raw)]
pub fn btreemap_insert_u64_blob_8_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<u64, Blob<8>>(btree)
}

#[bench(raw)]
pub fn btreemap_insert_blob_8_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    insert_helper::<Blob<8>, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_insert_blob_8_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    insert_helper::<Blob<8>, u64>(btree)
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
        let mut i = 0u64;
        for value in values {
            btree.insert(i, value);
            i += 1;
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

// Benchmarks removing keys from a BTreeMap.
bench_tests! {
    // x1024
    btreemap_remove_blob_4_1024,    remove_blob_helper,          4, 1024;
    btreemap_remove_blob_4_1024_v2, remove_blob_helper_v2,       4, 1024;
    btreemap_remove_blob_8_1024,    remove_blob_helper,          8, 1024;
    btreemap_remove_blob_8_1024_v2, remove_blob_helper_v2,       8, 1024;
    btreemap_remove_blob_16_1024,    remove_blob_helper,        16, 1024;
    btreemap_remove_blob_16_1024_v2, remove_blob_helper_v2,     16, 1024;
    btreemap_remove_blob_32_1024,    remove_blob_helper,        32, 1024;
    btreemap_remove_blob_32_1024_v2, remove_blob_helper_v2,     32, 1024;
    btreemap_remove_blob_64_1024,    remove_blob_helper,        64, 1024;
    btreemap_remove_blob_64_1024_v2, remove_blob_helper_v2,     64, 1024;
    btreemap_remove_blob_128_1024,    remove_blob_helper,      128, 1024;
    btreemap_remove_blob_128_1024_v2, remove_blob_helper_v2,   128, 1024;
    btreemap_remove_blob_256_1024,    remove_blob_helper,      256, 1024;
    btreemap_remove_blob_256_1024_v2, remove_blob_helper_v2,   256, 1024;
    btreemap_remove_blob_512_1024,    remove_blob_helper,      512, 1024;
    btreemap_remove_blob_512_1024_v2, remove_blob_helper_v2,   512, 1024;
    btreemap_remove_blob_1024_1024,    remove_blob_helper,    1024, 1024;
    btreemap_remove_blob_1024_1024_v2, remove_blob_helper_v2, 1024, 1024;
}

#[bench(raw)]
pub fn btreemap_remove_u64_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<u64, u64>(btree)
}
#[bench(raw)]
pub fn btreemap_remove_u64_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<u64, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_remove_u64_blob_8() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<u64, Blob<8>>(btree)
}
#[bench(raw)]
pub fn btreemap_remove_u64_blob_8_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<u64, Blob<8>>(btree)
}

#[bench(raw)]
pub fn btreemap_remove_blob_8_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    remove_helper::<Blob<8>, u64>(btree)
}
#[bench(raw)]
pub fn btreemap_remove_blob_8_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    remove_helper::<Blob<8>, u64>(btree)
}

// Benchmarks getting keys from a BTreeMap.
bench_tests! {
    // x4
    btreemap_get_blob_4_4,    get_blob_helper,          4, 4;
    btreemap_get_blob_4_4_v2, get_blob_helper_v2,       4, 4;
    btreemap_get_blob_8_4,    get_blob_helper,          8, 4;
    btreemap_get_blob_8_4_v2, get_blob_helper_v2,       8, 4;
    btreemap_get_blob_16_4,    get_blob_helper,        16, 4;
    btreemap_get_blob_16_4_v2, get_blob_helper_v2,     16, 4;
    btreemap_get_blob_32_4,    get_blob_helper,        32, 4;
    btreemap_get_blob_32_4_v2, get_blob_helper_v2,     32, 4;
    btreemap_get_blob_64_4,    get_blob_helper,        64, 4;
    btreemap_get_blob_64_4_v2, get_blob_helper_v2,     64, 4;
    btreemap_get_blob_128_4,    get_blob_helper,      128, 4;
    btreemap_get_blob_128_4_v2, get_blob_helper_v2,   128, 4;
    btreemap_get_blob_256_4,    get_blob_helper,      256, 4;
    btreemap_get_blob_256_4_v2, get_blob_helper_v2,   256, 4;
    btreemap_get_blob_512_4,    get_blob_helper,      512, 4;
    btreemap_get_blob_512_4_v2, get_blob_helper_v2,   512, 4;
    btreemap_get_blob_1024_4,    get_blob_helper,    1024, 4;
    btreemap_get_blob_1024_4_v2, get_blob_helper_v2, 1024, 4;
    btreemap_get_blob_1024_4_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 4;

    // x8
    btreemap_get_blob_4_8,    get_blob_helper,          4, 8;
    btreemap_get_blob_4_8_v2, get_blob_helper_v2,       4, 8;
    btreemap_get_blob_8_8,    get_blob_helper,          8, 8;
    btreemap_get_blob_8_8_v2, get_blob_helper_v2,       8, 8;
    btreemap_get_blob_16_8,    get_blob_helper,        16, 8;
    btreemap_get_blob_16_8_v2, get_blob_helper_v2,     16, 8;
    btreemap_get_blob_32_8,    get_blob_helper,        32, 8;
    btreemap_get_blob_32_8_v2, get_blob_helper_v2,     32, 8;
    btreemap_get_blob_64_8,    get_blob_helper,        64, 8;
    btreemap_get_blob_64_8_v2, get_blob_helper_v2,     64, 8;
    btreemap_get_blob_128_8,    get_blob_helper,      128, 8;
    btreemap_get_blob_128_8_v2, get_blob_helper_v2,   128, 8;
    btreemap_get_blob_256_8,    get_blob_helper,      256, 8;
    btreemap_get_blob_256_8_v2, get_blob_helper_v2,   256, 8;
    btreemap_get_blob_512_8,    get_blob_helper,      512, 8;
    btreemap_get_blob_512_8_v2, get_blob_helper_v2,   512, 8;
    btreemap_get_blob_1024_8,    get_blob_helper,    1024, 8;
    btreemap_get_blob_1024_8_v2, get_blob_helper_v2, 1024, 8;
    btreemap_get_blob_1024_8_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 8;

    // x16
    btreemap_get_blob_4_16,    get_blob_helper,          4, 16;
    btreemap_get_blob_4_16_v2, get_blob_helper_v2,       4, 16;
    btreemap_get_blob_8_16,    get_blob_helper,          8, 16;
    btreemap_get_blob_8_16_v2, get_blob_helper_v2,       8, 16;
    btreemap_get_blob_16_16,    get_blob_helper,        16, 16;
    btreemap_get_blob_16_16_v2, get_blob_helper_v2,     16, 16;
    btreemap_get_blob_32_16,    get_blob_helper,        32, 16;
    btreemap_get_blob_32_16_v2, get_blob_helper_v2,     32, 16;
    btreemap_get_blob_64_16,    get_blob_helper,        64, 16;
    btreemap_get_blob_64_16_v2, get_blob_helper_v2,     64, 16;
    btreemap_get_blob_128_16,    get_blob_helper,      128, 16;
    btreemap_get_blob_128_16_v2, get_blob_helper_v2,   128, 16;
    btreemap_get_blob_256_16,    get_blob_helper,      256, 16;
    btreemap_get_blob_256_16_v2, get_blob_helper_v2,   256, 16;
    btreemap_get_blob_512_16,    get_blob_helper,      512, 16;
    btreemap_get_blob_512_16_v2, get_blob_helper_v2,   512, 16;
    btreemap_get_blob_1024_16,    get_blob_helper,    1024, 16;
    btreemap_get_blob_1024_16_v2, get_blob_helper_v2, 1024, 16;
    btreemap_get_blob_1024_16_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 16;

    // x32
    btreemap_get_blob_4_32,    get_blob_helper,          4, 32;
    btreemap_get_blob_4_32_v2, get_blob_helper_v2,       4, 32;
    btreemap_get_blob_8_32,    get_blob_helper,          8, 32;
    btreemap_get_blob_8_32_v2, get_blob_helper_v2,       8, 32;
    btreemap_get_blob_16_32,    get_blob_helper,        16, 32;
    btreemap_get_blob_16_32_v2, get_blob_helper_v2,     16, 32;
    btreemap_get_blob_32_32,    get_blob_helper,        32, 32;
    btreemap_get_blob_32_32_v2, get_blob_helper_v2,     32, 32;
    btreemap_get_blob_64_32,    get_blob_helper,        64, 32;
    btreemap_get_blob_64_32_v2, get_blob_helper_v2,     64, 32;
    btreemap_get_blob_128_32,    get_blob_helper,      128, 32;
    btreemap_get_blob_128_32_v2, get_blob_helper_v2,   128, 32;
    btreemap_get_blob_256_32,    get_blob_helper,      256, 32;
    btreemap_get_blob_256_32_v2, get_blob_helper_v2,   256, 32;
    btreemap_get_blob_512_32,    get_blob_helper,      512, 32;
    btreemap_get_blob_512_32_v2, get_blob_helper_v2,   512, 32;
    btreemap_get_blob_1024_32,    get_blob_helper,    1024, 32;
    btreemap_get_blob_1024_32_v2, get_blob_helper_v2, 1024, 32;
    btreemap_get_blob_1024_32_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 32;

    // x64
    btreemap_get_blob_4_64,    get_blob_helper,          4, 64;
    btreemap_get_blob_4_64_v2, get_blob_helper_v2,       4, 64;
    btreemap_get_blob_8_64,    get_blob_helper,          8, 64;
    btreemap_get_blob_8_64_v2, get_blob_helper_v2,       8, 64;
    btreemap_get_blob_16_64,    get_blob_helper,        16, 64;
    btreemap_get_blob_16_64_v2, get_blob_helper_v2,     16, 64;
    btreemap_get_blob_32_64,    get_blob_helper,        32, 64;
    btreemap_get_blob_32_64_v2, get_blob_helper_v2,     32, 64;
    btreemap_get_blob_64_64,    get_blob_helper,        64, 64;
    btreemap_get_blob_64_64_v2, get_blob_helper_v2,     64, 64;
    btreemap_get_blob_128_64,    get_blob_helper,      128, 64;
    btreemap_get_blob_128_64_v2, get_blob_helper_v2,   128, 64;
    btreemap_get_blob_256_64,    get_blob_helper,      256, 64;
    btreemap_get_blob_256_64_v2, get_blob_helper_v2,   256, 64;
    btreemap_get_blob_512_64,    get_blob_helper,      512, 64;
    btreemap_get_blob_512_64_v2, get_blob_helper_v2,   512, 64;
    btreemap_get_blob_1024_64,    get_blob_helper,    1024, 64;
    btreemap_get_blob_1024_64_v2, get_blob_helper_v2, 1024, 64;
    btreemap_get_blob_1024_64_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 64;

    // x128
    btreemap_get_blob_4_128,    get_blob_helper,          4, 128;
    btreemap_get_blob_4_128_v2, get_blob_helper_v2,       4, 128;
    btreemap_get_blob_8_128,    get_blob_helper,          8, 128;
    btreemap_get_blob_8_128_v2, get_blob_helper_v2,       8, 128;
    btreemap_get_blob_16_128,    get_blob_helper,        16, 128;
    btreemap_get_blob_16_128_v2, get_blob_helper_v2,     16, 128;
    btreemap_get_blob_32_128,    get_blob_helper,        32, 128;
    btreemap_get_blob_32_128_v2, get_blob_helper_v2,     32, 128;
    btreemap_get_blob_64_128,    get_blob_helper,        64, 128;
    btreemap_get_blob_64_128_v2, get_blob_helper_v2,     64, 128;
    btreemap_get_blob_128_128,    get_blob_helper,      128, 128;
    btreemap_get_blob_128_128_v2, get_blob_helper_v2,   128, 128;
    btreemap_get_blob_256_128,    get_blob_helper,      256, 128;
    btreemap_get_blob_256_128_v2, get_blob_helper_v2,   256, 128;
    btreemap_get_blob_512_128,    get_blob_helper,      512, 128;
    btreemap_get_blob_512_128_v2, get_blob_helper_v2,   512, 128;
    btreemap_get_blob_1024_128,    get_blob_helper,    1024, 128;
    btreemap_get_blob_1024_128_v2, get_blob_helper_v2, 1024, 128;
    btreemap_get_blob_1024_128_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 128;

    // x256
    btreemap_get_blob_4_256,    get_blob_helper,          4, 256;
    btreemap_get_blob_4_256_v2, get_blob_helper_v2,       4, 256;
    btreemap_get_blob_8_256,    get_blob_helper,          8, 256;
    btreemap_get_blob_8_256_v2, get_blob_helper_v2,       8, 256;
    btreemap_get_blob_16_256,    get_blob_helper,        16, 256;
    btreemap_get_blob_16_256_v2, get_blob_helper_v2,     16, 256;
    btreemap_get_blob_32_256,    get_blob_helper,        32, 256;
    btreemap_get_blob_32_256_v2, get_blob_helper_v2,     32, 256;
    btreemap_get_blob_64_256,    get_blob_helper,        64, 256;
    btreemap_get_blob_64_256_v2, get_blob_helper_v2,     64, 256;
    btreemap_get_blob_128_256,    get_blob_helper,      128, 256;
    btreemap_get_blob_128_256_v2, get_blob_helper_v2,   128, 256;
    btreemap_get_blob_256_256,    get_blob_helper,      256, 256;
    btreemap_get_blob_256_256_v2, get_blob_helper_v2,   256, 256;
    btreemap_get_blob_512_256,    get_blob_helper,      512, 256;
    btreemap_get_blob_512_256_v2, get_blob_helper_v2,   512, 256;
    btreemap_get_blob_1024_256,    get_blob_helper,    1024, 256;
    btreemap_get_blob_1024_256_v2, get_blob_helper_v2, 1024, 256;
    btreemap_get_blob_1024_256_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 256;

    // x512
    btreemap_get_blob_4_512,    get_blob_helper,          4, 512;
    btreemap_get_blob_4_512_v2, get_blob_helper_v2,       4, 512;
    btreemap_get_blob_8_512,    get_blob_helper,          8, 512;
    btreemap_get_blob_8_512_v2, get_blob_helper_v2,       8, 512;
    btreemap_get_blob_16_512,    get_blob_helper,        16, 512;
    btreemap_get_blob_16_512_v2, get_blob_helper_v2,     16, 512;
    btreemap_get_blob_32_512,    get_blob_helper,        32, 512;
    btreemap_get_blob_32_512_v2, get_blob_helper_v2,     32, 512;
    btreemap_get_blob_64_512,    get_blob_helper,        64, 512;
    btreemap_get_blob_64_512_v2, get_blob_helper_v2,     64, 512;
    btreemap_get_blob_128_512,    get_blob_helper,      128, 512;
    btreemap_get_blob_128_512_v2, get_blob_helper_v2,   128, 512;
    btreemap_get_blob_256_512,    get_blob_helper,      256, 512;
    btreemap_get_blob_256_512_v2, get_blob_helper_v2,   256, 512;
    btreemap_get_blob_512_512,    get_blob_helper,      512, 512;
    btreemap_get_blob_512_512_v2, get_blob_helper_v2,   512, 512;
    btreemap_get_blob_1024_512,    get_blob_helper,    1024, 512;
    btreemap_get_blob_1024_512_v2, get_blob_helper_v2, 1024, 512;
    btreemap_get_blob_1024_512_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 512;

    // x1024
    btreemap_get_blob_4_1024,    get_blob_helper,          4, 1024;
    btreemap_get_blob_4_1024_v2, get_blob_helper_v2,       4, 1024;
    btreemap_get_blob_8_1024,    get_blob_helper,          8, 1024;
    btreemap_get_blob_8_1024_v2, get_blob_helper_v2,       8, 1024;
    btreemap_get_blob_16_1024,    get_blob_helper,        16, 1024;
    btreemap_get_blob_16_1024_v2, get_blob_helper_v2,     16, 1024;
    btreemap_get_blob_32_1024,    get_blob_helper,        32, 1024;
    btreemap_get_blob_32_1024_v2, get_blob_helper_v2,     32, 1024;
    btreemap_get_blob_64_1024,    get_blob_helper,        64, 1024;
    btreemap_get_blob_64_1024_v2, get_blob_helper_v2,     64, 1024;
    btreemap_get_blob_128_1024,    get_blob_helper,      128, 1024;
    btreemap_get_blob_128_1024_v2, get_blob_helper_v2,   128, 1024;
    btreemap_get_blob_256_1024,    get_blob_helper,      256, 1024;
    btreemap_get_blob_256_1024_v2, get_blob_helper_v2,   256, 1024;
    btreemap_get_blob_512_1024,    get_blob_helper,      512, 1024;
    btreemap_get_blob_512_1024_v2, get_blob_helper_v2,   512, 1024;
    btreemap_get_blob_1024_1024,    get_blob_helper,    1024, 1024;
    btreemap_get_blob_1024_1024_v2, get_blob_helper_v2, 1024, 1024;
    btreemap_get_blob_1024_1024_v2_mem_manager, get_blob_helper_v2_mem_manager, 1024, 1024;
}

#[bench(raw)]
pub fn btreemap_get_u64_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<u64, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_get_u64_u64_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<u64, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_get_u64_u64_v2_mem_manager() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    get_helper::<u64, u64>(btree)
}

#[bench(raw)]
pub fn btreemap_get_u64_blob_8() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<u64, Blob<8>>(btree)
}

#[bench(raw)]
pub fn btreemap_get_u64_blob_8_v2() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<u64, Blob<8>>(btree)
}

#[bench(raw)]
pub fn btreemap_get_blob_8_u64() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<Blob<8>, u64>(btree)
}

#[bench(raw)]
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

fn insert_blob_helper_v2_mem_manager<const K: usize, const V: usize>() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    insert_helper::<Blob<K>, Blob<V>>(btree)
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
fn get_blob_helper<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new_v1(DefaultMemoryImpl::default());
    get_helper::<Blob<K>, Blob<V>>(btree)
}

fn get_blob_helper_v2<const K: usize, const V: usize>() -> BenchResult {
    let btree = BTreeMap::new(DefaultMemoryImpl::default());
    get_helper::<Blob<K>, Blob<V>>(btree)
}

fn get_blob_helper_v2_mem_manager<const K: usize, const V: usize>() -> BenchResult {
    let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
    let btree = BTreeMap::new(memory_manager.get(MemoryId::new(42)));
    get_helper::<Blob<K>, Blob<V>>(btree)
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
