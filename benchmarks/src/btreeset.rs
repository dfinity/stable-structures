use canbench_rs::{bench, bench_fn, BenchResult};
use ic_stable_structures::storable::Blob;
use ic_stable_structures::{btreeset::BTreeSet, DefaultMemoryImpl, Storable};

// Define type alias for Blob<8>.
type Blob8 = Blob<8>;
type Blob16 = Blob<16>;
type Blob32 = Blob<32>;
type Blob64 = Blob<64>;
type Blob128 = Blob<128>;
type Blob256 = Blob<256>;
type Blob512 = Blob<512>;
type Blob1024 = Blob<1024>;

/// Helper macro to generate benchmarks.
macro_rules! bench_tests {
    ($( $fn_name:ident, $helper:ident, $k:expr );+ $(;)?) => {
        $(
            #[bench(raw)]
            pub fn $fn_name() -> BenchResult {
                $helper::<$k>()
            }
        )+
    };
}
// Profiles inserting a large number of keys into a BTreeSet.
fn insert_helper<K: Clone + Ord + Storable>() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());
    let num_keys = 10_000;

    bench_fn(|| {
        for i in 0..num_keys {
            let key = generate_key::<K>(i);
            btreeset.insert(key);
        }
    })
}

// Profiles removing a large number of keys from a BTreeSet.
fn remove_helper<K: Clone + Ord + Storable>() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());
    let num_keys = 10_000;

    for i in 0..num_keys {
        btreeset.insert(generate_key::<K>(i));
    }

    bench_fn(|| {
        for i in 0..num_keys {
            let key = generate_key::<K>(i);
            btreeset.remove(&key);
        }
    })
}

// Profiles iterating over a BTreeSet.
fn iter_helper<K: Clone + Ord + Storable>() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());

    for i in 0..10_000 {
        btreeset.insert(generate_key::<K>(i));
    }

    bench_fn(|| for _ in btreeset.iter() {})
}

// Profiles range queries on a BTreeSet.
fn range_helper<K: Clone + Ord + Storable>() -> BenchResult {
    let mut btreeset = BTreeSet::new(DefaultMemoryImpl::default());

    for i in 0..10_000 {
        btreeset.insert(generate_key::<K>(i));
    }

    let start = generate_key::<K>(2000);
    let end = generate_key::<K>(8000);

    bench_fn(|| for _ in btreeset.range(start..end) {})
}

// Profiles the union operation on two BTreeSets.
fn union_helper<K: Clone + Ord + Storable>() -> BenchResult {
    let mut btreeset1 = BTreeSet::new(DefaultMemoryImpl::default());
    let mut btreeset2 = BTreeSet::new(DefaultMemoryImpl::default());
    let num_keys = 1_000;

    for i in 0..num_keys {
        btreeset1.insert(generate_key::<K>(i));
        if i % 2 == 0 {
            btreeset2.insert(generate_key::<K>(i));
        }
    }

    bench_fn(|| for _ in btreeset1.union(&btreeset2) {})
}

// Profiles the intersection operation on two BTreeSets.
fn intersection_helper<K: Clone + Ord + Storable>() -> BenchResult {
    let mut btreeset1 = BTreeSet::init(DefaultMemoryImpl::default());
    let mut btreeset2 = BTreeSet::init(DefaultMemoryImpl::default());
    let num_keys = 1_000;

    for i in 0..num_keys {
        btreeset1.insert(generate_key::<K>(i));
        if i % 2 == 0 {
            btreeset2.insert(generate_key::<K>(i));
        }
    }

    bench_fn(|| for _ in btreeset1.intersection(&btreeset2) {})
}

// Generates keys directly based on the type `K`.
fn generate_key<K: Storable>(i: u32) -> K {
    K::from_bytes(std::borrow::Cow::Owned(i.to_be_bytes().to_vec()))
}

// Define benchmarks for various BTreeSet operations with different types.
bench_tests! {
    btreeset_insert_u32, insert_helper, u32;
    btreeset_insert_blob_8, insert_helper, Blob8;
    btreeset_remove_u32, remove_helper, u32;
    btreeset_remove_blob_8, remove_helper, Blob8;
    btreeset_iter_u32, iter_helper, u32;
    btreeset_iter_blob_8, iter_helper, Blob8;
    btreeset_range_u32, range_helper, u32;
    btreeset_range_blob_8, range_helper, Blob8;
}

// Add benchmarks for union and intersection with additional key types.
bench_tests! {
    btreeset_union_u32, union_helper, u32;
    btreeset_union_u64, union_helper, u64;
    btreeset_union_blob_8, union_helper, Blob8;
    btreeset_union_blob_16, union_helper, Blob16;
    btreeset_union_blob_32, union_helper, Blob32;
    btreeset_union_blob_64, union_helper, Blob64;
    btreeset_union_blob_128, union_helper, Blob128;
    btreeset_union_blob_256, union_helper, Blob256;
    btreeset_union_blob_512, union_helper, Blob512;
    btreeset_union_blob_1024, union_helper, Blob1024;
    btreeset_intersection_u32, intersection_helper, u32;
    btreeset_intersection_u64, intersection_helper, u64;
    btreeset_intersection_blob_8, intersection_helper, Blob8;
    btreeset_intersection_blob_16, intersection_helper, Blob16;
    btreeset_intersection_blob_32, intersection_helper, Blob32;
    btreeset_intersection_blob_64, intersection_helper, Blob64;
    btreeset_intersection_blob_128, intersection_helper, Blob128;
    btreeset_intersection_blob_256, intersection_helper, Blob256;
    btreeset_intersection_blob_512, intersection_helper, Blob512;
    btreeset_intersection_blob_1024, intersection_helper, Blob1024;
}
