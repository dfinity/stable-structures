use canbench_rs::{bench, bench_fn};
use ic_cdk::api::stable::WASM_PAGE_SIZE_IN_BYTES;
use ic_stable_structures::{
    memory_manager::{MemoryId, MemoryManager},
    BTreeMap, DefaultMemoryImpl, Memory,
};

const SIZE: usize = 100 * 1024 * 1024;
const VALUE: u8 = 37;

fn page_align(bytes: usize) -> u64 {
    bytes.div_ceil(WASM_PAGE_SIZE_IN_BYTES) as u64
}

fn init_memory(id: u8) -> impl ic_stable_structures::Memory {
    MemoryManager::init(DefaultMemoryImpl::default()).get(MemoryId::new(id))
}

fn ensure_memory_size(memory: &impl ic_stable_structures::Memory, size: usize) {
    let required = page_align(size);
    if memory.size() < required {
        memory.grow(required - memory.size());
    }
}

fn chunk_data(n: usize) -> Vec<Vec<u8>> {
    let chunk_size = SIZE / n;
    vec![VALUE; SIZE]
        .chunks(chunk_size)
        .map(|c| c.to_vec())
        .collect()
}

#[bench]
fn write_chunks_stable_1() {
    write_chunks_stable(30, 1);
}

#[bench]
fn write_chunks_stable_1k() {
    write_chunks_stable(31, 1_000);
}

#[bench]
fn write_chunks_stable_1m() {
    write_chunks_stable(32, 1_000_000);
}

fn write_chunks_stable(mem_id: u8, n: usize) {
    let memory = init_memory(mem_id);
    let chunks = chunk_data(n);
    let chunk_size = SIZE / n;

    bench_fn(|| {
        ensure_memory_size(&memory, SIZE);
        for (i, chunk) in chunks.iter().enumerate() {
            memory.write((i * chunk_size) as u64, chunk);
        }
    });
}

#[bench]
fn read_chunks_stable_1() {
    read_chunks_stable(40, 1);
}

#[bench]
fn read_chunks_stable_1k() {
    read_chunks_stable(41, 1_000);
}

#[bench]
fn read_chunks_stable_1m() {
    read_chunks_stable(44, 1_000_000);
}

fn read_chunks_stable(mem_id: u8, n: usize) {
    write_chunks_stable(mem_id, n);

    let memory = init_memory(mem_id);
    let chunk_size = SIZE / n;
    let mut buf = vec![0u8; chunk_size];

    bench_fn(|| {
        for i in 0..n {
            memory.read((i * chunk_size) as u64, &mut buf);
        }
    });
}

#[bench]
fn write_chunks_btreemap_1() {
    write_chunks_btreemap(10, 1);
}

#[bench]
fn write_chunks_btreemap_1k() {
    write_chunks_btreemap(11, 1_000);
}

#[bench]
fn write_chunks_btreemap_1m() {
    write_chunks_btreemap(12, 1_000_000);
}

fn write_chunks_btreemap(mem_id: u8, n: usize) {
    let mut map = BTreeMap::init(init_memory(mem_id));
    let chunks = chunk_data(n);

    bench_fn(|| {
        for (i, chunk) in chunks.into_iter().enumerate() {
            map.insert(i as u32, chunk);
        }
    });
}

#[bench]
fn read_chunks_btreemap_1() {
    read_chunks_btreemap(20, 1);
}

#[bench]
fn read_chunks_btreemap_1k() {
    read_chunks_btreemap(21, 1_000);
}

#[bench]
fn read_chunks_btreemap_1m() {
    read_chunks_btreemap(22, 1_000_000);
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

fn main() {}
