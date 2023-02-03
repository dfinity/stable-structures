mod btreemap;
mod memory_manager;

/// Returns the number of instructions consumed by the given function.
pub(crate) fn count_instructions<R>(f: impl FnOnce() -> R) -> u64 {
    let start = ic_cdk::api::performance_counter(0);
    profiler::reset();
    f();
    let total_instructions = ic_cdk::api::performance_counter(0) - start;

    let profiling_results: std::collections::BTreeMap<_, _> = profiler::get_results()
        .into_iter()
        .map(|(k, v)| {
            (
                k,
                format!("{} ({}%)", format_num(v), ((v * 100) / total_instructions)),
            )
        })
        .collect();
    ic_cdk::api::print(&format!("{:#?}", profiling_results));
    total_instructions
}

fn format_num(num: u64) -> String {
    num.to_string()
        .as_bytes()
        .rchunks(3)
        .rev()
        .map(std::str::from_utf8)
        .collect::<Result<Vec<&str>, _>>()
        .unwrap()
        .join("_")
}

fn main() {}
