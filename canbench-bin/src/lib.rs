//! A module for running benchmarks.
use canbench::BenchResult;
use candid::Decode;
use colored::Colorize;
use flate2::read::GzDecoder;
use std::{
    collections::BTreeMap,
    env,
    fs::File,
    io::{Read, Write},
    path::{Path, PathBuf},
    process::Command,
};
use wasmparser::Parser as WasmParser;

// The prefix benchmarks are expected to have in their name.
// Other queries exposed by the canister are ignored.
const BENCH_PREFIX: &str = "__canbench__";

/// Runs the benchmarks on the canister available in the provided `canister_wasm_path`.
pub fn run_benchmarks(
    canister_wasm_path: &PathBuf,
    pattern: Option<String>,
    persist: bool,
    results_file: &PathBuf,
) {
    // Parse the Wasm to determine all the benchmarks to run.
    // All query endpoints are assumed to be benchmarks.
    let benchmark_canister_wasm = std::fs::read(canister_wasm_path).unwrap();

    let prefix = format!("canister_query {BENCH_PREFIX}");

    let benchmark_fns: Vec<_> = WasmParser::new(0)
        .parse_all(&benchmark_canister_wasm)
        .filter_map(|section| match section {
            Ok(wasmparser::Payload::ExportSection(export_section)) => {
                let queries: Vec<_> = export_section
                    .into_iter()
                    .filter_map(|export| {
                        if let Ok(export) = export {
                            if export.name.starts_with(&prefix) {
                                return Some(
                                    export
                                        .name
                                        .split(&prefix)
                                        .last()
                                        .expect("query must have a name."),
                                );
                            }
                        }

                        None
                    })
                    .collect();

                Some(queries)
            }
            _ => None,
        })
        .flatten()
        .collect();

    maybe_download_drun();

    let current_results = read_current_results(results_file);

    let mut results = BTreeMap::new();

    for bench_fn in benchmark_fns {
        if let Some(pattern) = &pattern {
            if !bench_fn.contains(pattern) {
                continue;
            }
        }

        println!();
        println!("---------------------------------------------------");
        println!();

        let result = run_benchmark(canister_wasm_path, &bench_fn);

        // Compare result to previous result if that exists.
        if let Some(current_result) = current_results.get(&bench_fn.to_string()) {
            println!("Benchmark: {}", bench_fn.bold());
            compare(current_result, &result);
        } else {
            println!("Benchmark: {} {}", bench_fn.bold(), "(new)".blue().bold());
            let yaml = serde_yaml::to_string(&result).unwrap();
            println!("{}", yaml);
        }

        results.insert(bench_fn, result);
    }

    // Persist the result if requested.
    if persist {
        // Open a file in write-only mode, returns `io::Result<File>`
        let mut file = File::create(results_file).unwrap();
        file.write_all(serde_yaml::to_string(&results).unwrap().as_bytes())
            .unwrap();
        println!(
            "Successfully persisted results to {}",
            results_file.display()
        );
    }
}

// Path to the canbench directory where we keep internal data.
fn canbench_dir() -> PathBuf {
    PathBuf::new()
        .join(env::current_dir().unwrap())
        .join(".canbench")
}

// Path to drun.
fn drun_path() -> PathBuf {
    canbench_dir().join("drun")
}

// Downloads drun if it's not already downloaded.
fn maybe_download_drun() {
    const DRUN_LINUX_SHA: &str = "7bf08d5f1c1a7cd44f62c03f8554f07aa2430eb3ae81c7c0a143a68ff52dc7f7";
    const DRUN_MAC_SHA: &str = "57b506d05a6f42f7461198f79f648ad05434c72f3904834db2ced30853d01a62";

    if drun_path().exists() {
        // Drun found. Verify that it's the version we expect it to be.
        let expected_sha = match env::consts::OS {
            "linux" => DRUN_LINUX_SHA,
            "macos" => DRUN_MAC_SHA,
            _ => panic!("only linux and macos are currently supported."),
        };

        let drun_sha = sha256::try_digest(drun_path()).unwrap();

        if drun_sha == expected_sha {
            // Shas match. No need to download drun.
            return;
        }
    }

    // The expected version of drun isn't present. Download it.
    download_drun();
}

fn download_drun() {
    const DRUN_URL_PREFIX: &str =
        "https://github.com/dfinity/ic/releases/download/release-2023-09-27_23-01%2Bquic/drun-x86_64-";

    println!("Downloading drun (will be cached for future uses)...");

    // Create the canbench directory if it doesn't exist.
    std::fs::create_dir_all(canbench_dir()).unwrap();

    let os = if cfg!(target_os = "linux") {
        "linux"
    } else if cfg!(target_os = "macos") {
        "darwin"
    } else {
        panic!("Unsupported operating system");
    };

    let url = format!("{}{}.gz", DRUN_URL_PREFIX, os);
    let drun_compressed = reqwest::blocking::get(url)
        .unwrap()
        .bytes()
        .expect("Failed to download drun");

    let mut decoder = GzDecoder::new(&drun_compressed[..]);
    let mut file = File::create(drun_path()).expect("Failed to create drun file");

    std::io::copy(&mut decoder, &mut file).expect("Failed to write drun file");

    // Make the file executable.
    Command::new("chmod")
        .arg("+x")
        .arg(drun_path())
        .status()
        .unwrap();
}

// Runs the given benchmark.
fn run_benchmark(canister_wasm_path: &Path, bench_fn: &str) -> BenchResult {
    // drun is used for running the benchmark.
    // First, we create a temporary file with steps for drun to execute the benchmark.
    let mut temp_file = tempfile::Builder::new().tempfile().unwrap();
    write!(
        temp_file,
        "create
install rwlgt-iiaaa-aaaaa-aaaaa-cai {} \"\"
query rwlgt-iiaaa-aaaaa-aaaaa-cai {}{} \"DIDL\x00\x00\"",
        canister_wasm_path.display(),
        BENCH_PREFIX,
        bench_fn
    )
    .unwrap();

    // Run the benchmark with drun.
    let drun_output = Command::new(drun_path())
        .args(vec![
            temp_file.into_temp_path().to_str().unwrap(),
            "--instruction-limit",
            "99999999999999",
        ])
        .output()
        .unwrap();

    // Extract the hex response.
    let result_hex = String::from_utf8(drun_output.stdout)
        .unwrap()
        .split_whitespace()
        .last()
        .unwrap()
        .to_string();

    // Decode the response.
    Decode!(
        &hex::decode(&result_hex[2..]).expect(&format!(
            "error parsing result of benchmark {}. Result: {}",
            bench_fn, result_hex
        )),
        BenchResult
    )
    .expect("error decoding benchmark result {:?}")
}

// Prints a measurement along with its percentage change relative to the old value.
fn print_measurement(measurement: &str, value: u64, diff: f64) {
    if diff == 0.0 {
        println!("    {measurement}: {value} ({:.2}%) (no change)", diff);
    } else if diff.abs() < 2.0 {
        println!(
            "    {measurement}: {value} ({:.2}%) (change within noise threshold)",
            diff
        );
    } else if diff > 0.0 {
        println!(
            "    {}",
            format!("{}: {value} (regressed by {:.2}%)", measurement, diff,)
                .red()
                .bold()
        );
    } else {
        println!(
            "    {}",
            format!("{}: {value} (improved by {:.2}%)", measurement, diff.abs(),)
                .green()
                .bold()
        );
    }
}

// Prints out a measurement of the new value along with a comparison with the old value.
fn compare(old: &BenchResult, new: &BenchResult) {
    println!("  measurements:");
    for (measurement, value) in new.measurements.iter() {
        match old.measurements.get(measurement) {
            Some(old_value) => {
                let diff = ((*value as f64 - *old_value as f64) / *old_value as f64) * 100.0;
                print_measurement(measurement, *value, diff);
            }
            None => println!("    {measurement}: {value} (new)"),
        }
    }
}

fn read_current_results(results_file: &PathBuf) -> BTreeMap<String, BenchResult> {
    // Create a path to the desired file
    let mut file = match File::open(results_file) {
        Err(_) => {
            // No current results found.
            return BTreeMap::new();
        }
        Ok(file) => file,
    };

    // Read the current results.
    let mut results_str = String::new();
    file.read_to_string(&mut results_str)
        .expect("error reading results file");
    serde_yaml::from_str(&results_str).unwrap()
}
