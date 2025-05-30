use canbench_rs::{bench, bench_fn, BenchResult};
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
use ic_stable_structures::{DefaultMemoryImpl, Memory};

const WASM_PAGE_SIZE: usize = 65536;
const MB: usize = 1024 * 1024;
const MB_IN_PAGES: usize = MB / WASM_PAGE_SIZE;

/// Benchmarks accessing stable memory without using a `MemoryManager` to establish a baseline.
#[bench(raw)]
pub fn memory_manager_baseline() -> BenchResult {
    // A buffer of 100MiB.
    let buf_size = 100 * MB;
    let buf_size_in_pages = (100 * MB_IN_PAGES) as u64;
    let mut buf = vec![0; buf_size];

    let memory = DefaultMemoryImpl::default();
    bench_fn(|| {
        // Write the buffer 5 times consecutively in memory.
        for i in 0..5 {
            memory.grow(buf_size_in_pages);
            memory.write(i * buf_size as u64, &buf);
        }

        // Read the buffers from memory.
        for i in 0..5 {
            memory.read(i * buf_size as u64, &mut buf);
        }
    })
}

/// Benchmarks the `MemoryManager` by writing a 100MiB buffer to 5 memories.
/// The virtual memories of the `MemoryManager` are written in small chunks so that they are
/// interleaved in the underlying stable memory.
#[bench(raw)]
pub fn memory_manager_overhead() -> BenchResult {
    // A buffer of 100MiB.
    let num_chunks = 100;
    let buf_size = num_chunks * MB;
    let mut buf = vec![0; buf_size];

    let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    let num_memories = 5;
    bench_fn(|| {
        for i in 0..num_memories {
            let memory = mem_mgr.get(MemoryId::new(i));
            for j in 0..num_chunks {
                memory.grow(MB_IN_PAGES as u64);
                memory.write((j * MB) as u64, &buf[j * MB..(j + 1) * MB]);
            }
        }

        for i in 0..num_memories {
            let memory = mem_mgr.get(MemoryId::new(i));
            memory.read(0, &mut buf);
        }
    })
}

/// Benchmarks the `MemoryManager`'s `grow` method.
#[bench(raw)]
pub fn memory_manager_grow() -> BenchResult {
    let mem_mgr = MemoryManager::init_with_bucket_size(DefaultMemoryImpl::default(), 1);

    let buckets_per_memory = 32000;

    let memory = mem_mgr.get(MemoryId::new(0));

    bench_fn(|| {
        for _ in 0..buckets_per_memory {
            memory.grow(1);
        }
    })
}

fn main() {}
