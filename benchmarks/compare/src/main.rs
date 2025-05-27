use canbench_rs::{bench, bench_fn};
use ic_cdk::api::stable::WASM_PAGE_SIZE_IN_BYTES;
use ic_stable_structures::{
    memory_manager::{MemoryId, MemoryManager},
    BTreeMap, DefaultMemoryImpl, Memory,
};

const TOTAL_SIZE: usize = 100 * 1024 * 1024; // 100 MiB
const K: usize = 1_000;
const M: usize = 1_000_000;

fn init_memory(id: u8) -> impl Memory {
    MemoryManager::init(DefaultMemoryImpl::default()).get(MemoryId::new(id))
}

fn ensure_memory_size(memory: &impl Memory, size: usize) {
    let required = size.div_ceil(WASM_PAGE_SIZE_IN_BYTES) as u64;
    if memory.size() < required {
        memory.grow(required - memory.size());
    }
}

fn chunk_data(n: usize) -> Vec<Vec<u8>> {
    let chunk_size = TOTAL_SIZE / n;
    (0..n).map(|_| vec![37; chunk_size]).collect()
}

// Stable memory benchmarks

fn write_chunks_stable(mem_id: u8, n: usize) {
    let memory = init_memory(mem_id);
    let chunks = chunk_data(n);
    let chunk_size = TOTAL_SIZE / n;

    bench_fn(|| {
        ensure_memory_size(&memory, TOTAL_SIZE);
        for (i, chunk) in chunks.iter().enumerate() {
            memory.write((i * chunk_size) as u64, chunk);
        }
    });
}

fn read_chunks_stable(mem_id: u8, n: usize) {
    write_chunks_stable(mem_id, n);
    let memory = init_memory(mem_id);
    let chunk_size = TOTAL_SIZE / n;
    let mut buf = vec![0u8; chunk_size];

    bench_fn(|| {
        for i in 0..n {
            memory.read((i * chunk_size) as u64, &mut buf);
        }
    });
}

// BTreeMap benchmarks

fn write_chunks_btreemap(mem_id: u8, n: usize) {
    let mut map = BTreeMap::init(init_memory(mem_id));
    let chunks = chunk_data(n);

    bench_fn(|| {
        for (i, chunk) in chunks.into_iter().enumerate() {
            map.insert(i as u32, chunk);
        }
    });
}

fn read_chunks_btreemap(mem_id: u8, n: usize) {
    write_chunks_btreemap(mem_id, n);
    let map: BTreeMap<_, Vec<u8>, _> = BTreeMap::init(init_memory(mem_id));
    bench_fn(|| {
        for i in 0..n {
            let _ = map.get(&(i as u32));
        }
    });
}

// Macro to define a single benchmark function
macro_rules! bench_case {
    ($name:ident, $func:ident, $mem_id:expr, $n:expr) => {
        #[bench]
        fn $name() {
            $func($mem_id, $n);
        }
    };
}

// Stable Memory benchmarks
bench_case!(write_chunks_stable_1, write_chunks_stable, 10, 1);
bench_case!(write_chunks_stable_1k, write_chunks_stable, 11, K);
bench_case!(write_chunks_stable_1m, write_chunks_stable, 12, M);
bench_case!(read_chunks_stable_1, read_chunks_stable, 20, 1);
bench_case!(read_chunks_stable_1k, read_chunks_stable, 21, K);
bench_case!(read_chunks_stable_1m, read_chunks_stable, 22, M);

// BTreeMap benchmarks
bench_case!(write_chunks_btreemap_1, write_chunks_btreemap, 30, 1);
bench_case!(write_chunks_btreemap_1k, write_chunks_btreemap, 31, K);
bench_case!(write_chunks_btreemap_1m, write_chunks_btreemap, 32, M);
bench_case!(read_chunks_btreemap_1, read_chunks_btreemap, 40, 1);
bench_case!(read_chunks_btreemap_1k, read_chunks_btreemap, 41, K);
bench_case!(read_chunks_btreemap_1m, read_chunks_btreemap, 42, M);

fn main() {}
