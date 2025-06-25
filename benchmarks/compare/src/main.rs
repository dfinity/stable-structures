use benchmarks::vec::BoundedVecN;
use canbench_rs::{bench, bench_fn};
use ic_cdk::api::stable::WASM_PAGE_SIZE_IN_BYTES;
use ic_stable_structures::{
    memory_manager::{MemoryId, MemoryManager},
    BTreeMap, DefaultMemoryImpl, Memory, Vec as StableVec,
};

const TOTAL_SIZE: usize = 100 * 1024 * 1024; // 100 MiB
const K: usize = 1_000;
const M: usize = 1_000_000;

fn init_memory(id: u8) -> impl Memory {
    MemoryManager::init(DefaultMemoryImpl::default()).get(MemoryId::new(id))
}

fn ensure_memory_size(memory: &impl Memory, size: usize) {
    let required = size.div_ceil(WASM_PAGE_SIZE_IN_BYTES as usize) as u64;
    if memory.size() < required {
        memory.grow(required - memory.size());
    }
}

const fn chunk_size<const N: usize>() -> usize {
    TOTAL_SIZE / N
}

fn chunk_data(n: usize) -> Vec<Vec<u8>> {
    let chunk_size = TOTAL_SIZE / n;
    (0..n).map(|_| vec![37; chunk_size]).collect()
}

// Stable Memory benchmarks

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

// StableVec benchmarks

fn write_chunks_vec<const CHUNK_SIZE: usize>(mem_id: u8, n: usize) {
    let vec: StableVec<BoundedVecN<CHUNK_SIZE>, _> = StableVec::new(init_memory(mem_id));
    let chunks: Vec<_> = chunk_data(n).iter().map(|v| BoundedVecN::from(v)).collect();

    bench_fn(|| {
        for chunk in &chunks {
            vec.push(chunk);
        }
    });
}

fn read_chunks_vec<const CHUNK_SIZE: usize>(mem_id: u8, n: usize) {
    write_chunks_vec::<CHUNK_SIZE>(mem_id, n);
    let vec: StableVec<BoundedVecN<CHUNK_SIZE>, _> = StableVec::init(init_memory(mem_id));

    bench_fn(|| {
        for i in 0..n as u64 {
            let _ = vec.get(i);
        }
    });
}

// Benchmark macros

macro_rules! bench_case {
    ($name:ident, $func:ident, $mem_id:expr, $n:expr) => {
        #[bench]
        fn $name() {
            $func($mem_id, $n);
        }
    };
}

macro_rules! bench_case_sized {
    ($name:ident, $func:ident, $mem_id:expr, $n:expr) => {
        #[bench]
        fn $name() {
            const SIZE: usize = chunk_size::<$n>();
            $func::<SIZE>($mem_id, $n);
        }
    };
}

// Benchmark registrations

// Stable Memory
bench_case!(write_chunks_stable_1, write_chunks_stable, 10, 1);
bench_case!(write_chunks_stable_1k, write_chunks_stable, 11, K);
bench_case!(write_chunks_stable_1m, write_chunks_stable, 12, M);
bench_case!(read_chunks_stable_1, read_chunks_stable, 20, 1);
bench_case!(read_chunks_stable_1k, read_chunks_stable, 21, K);
bench_case!(read_chunks_stable_1m, read_chunks_stable, 22, M);

// BTreeMap
bench_case!(write_chunks_btreemap_1, write_chunks_btreemap, 30, 1);
bench_case!(write_chunks_btreemap_1k, write_chunks_btreemap, 31, K);
bench_case!(write_chunks_btreemap_1m, write_chunks_btreemap, 32, M);
bench_case!(read_chunks_btreemap_1, read_chunks_btreemap, 40, 1);
bench_case!(read_chunks_btreemap_1k, read_chunks_btreemap, 41, K);
bench_case!(read_chunks_btreemap_1m, read_chunks_btreemap, 42, M);

// StableVec
bench_case_sized!(write_chunks_vec_1, write_chunks_vec, 50, 1);
bench_case_sized!(write_chunks_vec_1k, write_chunks_vec, 51, K);
bench_case_sized!(write_chunks_vec_1m, write_chunks_vec, 52, M);
bench_case_sized!(read_chunks_vec_1, read_chunks_vec, 60, 1);
bench_case_sized!(read_chunks_vec_1k, read_chunks_vec, 61, K);
bench_case_sized!(read_chunks_vec_1m, read_chunks_vec, 62, M);

fn main() {}
