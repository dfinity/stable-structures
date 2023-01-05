mod btreemap;
mod memory_manager;

/// Returns the number of instructions consumed by the given function.
pub(crate) fn count_instructions<R>(f: impl FnOnce() -> R) -> u64 {
    let start = ic_cdk::api::performance_counter(0);
    f();
    ic_cdk::api::performance_counter(0) - start
}

fn main() {}
