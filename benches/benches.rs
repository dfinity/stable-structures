use std::{
    collections::HashMap, env, path::PathBuf, process::Command, sync::Mutex, time::Duration,
};

use criterion::{measurement::Measurement, Criterion};

pub struct Instructions;
struct InstructionsFormatter;

impl Measurement for Instructions {
    type Intermediate = ();

    type Value = u64;

    fn start(&self) -> Self::Intermediate {
        panic!("Instruction measurements must be custom calculated");
    }

    fn end(&self, _i: Self::Intermediate) -> Self::Value {
        panic!("Instruction measurements must be custom calculated");
    }

    fn add(&self, v1: &Self::Value, v2: &Self::Value) -> Self::Value {
        v1 + v2
    }

    fn zero(&self) -> Self::Value {
        0
    }

    fn to_f64(&self, value: &Self::Value) -> f64 {
        *value as f64
    }

    fn formatter(&self) -> &dyn criterion::measurement::ValueFormatter {
        &InstructionsFormatter
    }
}

impl criterion::measurement::ValueFormatter for InstructionsFormatter {
    fn scale_values(&self, typical_value: f64, values: &mut [f64]) -> &'static str {
        if typical_value < 10_000.0 {
            return "Instructions";
        }
        if typical_value < 10_000_000.0 {
            for v in values {
                *v /= 1_000.0;
            }
            return "K Instructions";
        }
        if typical_value < 10_000_000_000.0 {
            for v in values {
                *v /= 1_000_000.0;
            }
            return "M Instructions";
        }
        if typical_value < 10_000_000_000_000.0 {
            for v in values {
                *v /= 1_000_000_000.0;
            }
            return "B Instructions";
        }
        for v in values {
            *v /= 1_000_000_000_000.0;
        }
        "T Instructions"
    }

    fn scale_throughputs(
        &self,
        typical_value: f64,
        _throughput: &criterion::Throughput,
        values: &mut [f64],
    ) -> &'static str {
        self.scale_values(typical_value, values)
    }

    fn scale_for_machines(&self, _values: &mut [f64]) -> &'static str {
        "Instructions"
    }
}

fn dfx_project_dir() -> PathBuf {
    PathBuf::new()
        .join(env::var("CARGO_MANIFEST_DIR").unwrap())
        .join("benchmark-canisters")
}

struct DfxStarted;

impl DfxStarted {
    fn new() -> Self {
        assert!(Command::new("dfx")
            .args(["start", "--background", "--clean"])
            .current_dir(dfx_project_dir())
            .status()
            .unwrap()
            .success());
        Self
    }
}

impl Drop for DfxStarted {
    fn drop(&mut self) {
        assert!(Command::new("dfx")
            .arg("stop")
            .current_dir(dfx_project_dir())
            .status()
            .unwrap()
            .success());
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct DeployedCanister(&'static str);

impl DeployedCanister {
    fn new(name: &'static str) -> Self {
        assert!(Command::new("dfx")
            .args(["deploy", "--no-wallet", name])
            .current_dir(dfx_project_dir())
            .status()
            .unwrap()
            .success());
        Self(name)
    }

    fn name(&self) -> &'static str {
        self.0
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ExecutionArguments {
    canister: DeployedCanister,
    method: String,
    is_query: bool,
}

impl ExecutionArguments {
    fn new(canister: DeployedCanister, method: &str, is_query: bool) -> Self {
        Self {
            canister,
            method: method.to_string(),
            is_query,
        }
    }
}

lazy_static::lazy_static! {
    static ref BENCHMARK_CANISTER: DeployedCanister = DeployedCanister::new("benchmarks");
    static ref CACHED_RESULTS: Mutex<HashMap<ExecutionArguments, u64>> = Mutex::new(HashMap::new());
}

fn execution_instructions(arguments: ExecutionArguments) -> u64 {
    // Since execution will be deterministic and Criterion won't let us run it
    // only once, we'll cache the result of a given execution and immediatelly
    // return the same value on subsequent runs.
    if let Some(&result) = CACHED_RESULTS.lock().unwrap().get(&arguments) {
        return result;
    }

    let mut args = vec![
        "canister",
        "call",
        arguments.canister.name(),
        &arguments.method,
    ];
    if arguments.is_query {
        args.push("--query");
    };

    let output = Command::new("dfx")
        .current_dir(dfx_project_dir())
        .args(args)
        .output()
        .unwrap();
    assert!(output.status.success());
    let output = String::from_utf8(output.stdout).unwrap();

    // Convert result formatted as "(1_000_000 : nat64)" to u64.
    let result = output
        .trim()
        .strip_prefix('(')
        .unwrap()
        .strip_suffix(" : nat64)")
        .unwrap()
        .chars()
        .filter(|&c| c != '_')
        .collect::<String>()
        .parse()
        .unwrap();
    CACHED_RESULTS.lock().unwrap().insert(arguments, result);
    result
}

fn bench_function(
    c: &mut Criterion<Instructions>,
    canister: DeployedCanister,
    method: &str,
    is_query: bool,
) {
    c.bench_function(method, |b| {
        b.iter_custom(|iters| {
            // Each run will have the same result, so just do it once and
            // multiply by the number of iterations.
            iters * execution_instructions(ExecutionArguments::new(canister, method, is_query))
        })
    });
}

pub fn criterion_benchmark(c: &mut Criterion<Instructions>) {
    // MemoryManager benchmarks
    bench_function(c, *BENCHMARK_CANISTER, "memory_manager_baseline", true);
    bench_function(c, *BENCHMARK_CANISTER, "memory_manager_overhead", true);

    // BTree benchmarks
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_insert_blob_4_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_insert_blob_8_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_insert_blob_16_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_insert_blob_32_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_insert_blob_64_1024", true);
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_insert_blob_128_1024",
        true,
    );

    // These tests are called as update calls as they exceed the instruction
    // limit for query calls.
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_insert_blob_256_1024",
        false,
    );
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_insert_blob_512_1024",
        false,
    );

    bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_4_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_8_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_16_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_32_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_64_1024", true);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_128_1024", true);
    // These tests go over the instruction limit, so we can't run them currently.
    // bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_256_1024", true);
    // bench_function(c, *BENCHMARK_CANISTER, "btreemap_get_blob_512_1024", true);

    bench_function(c, *BENCHMARK_CANISTER, "btreemap_remove_blob_4_1024", false);
    bench_function(c, *BENCHMARK_CANISTER, "btreemap_remove_blob_8_1024", false);
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_remove_blob_16_1024",
        false,
    );
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_remove_blob_32_1024",
        false,
    );
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_remove_blob_64_1024",
        false,
    );
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_remove_blob_128_1024",
        false,
    );
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_remove_blob_256_1024",
        false,
    );
    // This test goes over the instructions limit, so we can't run it currently.
    bench_function(
        c,
        *BENCHMARK_CANISTER,
        "btreemap_remove_blob_512_1024",
        false,
    );

    // Vec benchmarks
    bench_function(c, *BENCHMARK_CANISTER, "vec_insert_blob_4", false);
    bench_function(c, *BENCHMARK_CANISTER, "vec_insert_blob_8", false);
    bench_function(c, *BENCHMARK_CANISTER, "vec_insert_blob_16", false);
    bench_function(c, *BENCHMARK_CANISTER, "vec_insert_blob_32", false);
    bench_function(c, *BENCHMARK_CANISTER, "vec_insert_blob_128", false);

    bench_function(c, *BENCHMARK_CANISTER, "vec_get_blob_4", true);
    bench_function(c, *BENCHMARK_CANISTER, "vec_get_blob_8", true);
    bench_function(c, *BENCHMARK_CANISTER, "vec_get_blob_16", true);
    bench_function(c, *BENCHMARK_CANISTER, "vec_get_blob_32", true);
    bench_function(c, *BENCHMARK_CANISTER, "vec_get_blob_128", true);
}

fn benches() {
    let mut c = Criterion::default()
        .with_measurement(Instructions)
        // 10 is the smallest sample size allowed.
        .sample_size(10)
        // Should limit us to one warm-up run.
        .warm_up_time(Duration::from_millis(1))
        // Large enough to suppress warnings about not being able to complete 10
        // samples in time.
        .measurement_time(Duration::from_secs(300))
        .configure_from_args();
    criterion_benchmark(&mut c);
}

fn main() {
    let _dfx_started = DfxStarted::new();
    benches();
}
