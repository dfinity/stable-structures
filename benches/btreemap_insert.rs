use criterion::{criterion_group, criterion_main, Criterion};
use ic_stable_structures::{BTreeMap, FileMemory};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

fn btree_insert_bench() {
    // Use a file memory as that more closely mimics the environment of the IC.
    let mem = FileMemory::new(tempfile::tempfile().unwrap());
    let mut btree: BTreeMap<_, Vec<u8>, Vec<u8>> = BTreeMap::init_with_sizes(mem, 32, 8);

    let mut rng = ChaCha8Rng::seed_from_u64(1);

    // Insert 1k random elements into the btree.
    for _ in 0..1_000 {
        let random_bytes = rng.gen::<[u8; 32]>().to_vec();
        btree.insert(random_bytes, vec![]).unwrap();
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("BTreeMap::insert", |b| b.iter(|| btree_insert_bench()));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
