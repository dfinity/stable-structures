//! A script for running benchmarks on a canister.
//! To run this script, run `cargo bench`.
use candid::{CandidType, Decode};
use clap::Parser;
use colored::Colorize;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    env,
    fs::File,
    io::{Read, Write},
    path::PathBuf,
    process::Command,
};
use wasmparser::Parser as WasmParser;

// The file to persist benchmark results to.
const RESULTS_FILE: &str = "results.yml";

fn benchmarks_dir() -> PathBuf {
    PathBuf::new()
        .join(env::var("CARGO_MANIFEST_DIR").unwrap())
        .join("benchmarks")
}

#[derive(Debug, PartialEq, CandidType, Serialize, Deserialize)]
struct BenchResult {
    measurements: BTreeMap<String, u64>,
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

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    // If provided, only benchmarks that match this pattern will be executed.
    pattern: Option<String>,

    // A necessary flag to keep `cargo bench` happy.
    #[clap(long)]
    bench: bool,

    // Whether or not results should be persisted to disk.
    #[clap(long)]
    persist: bool,
}

fn read_current_results() -> BTreeMap<String, BenchResult> {
    // Create a path to the desired file
    let mut file = match File::open(benchmarks_dir().join(RESULTS_FILE)) {
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

fn main() {
    let args = Args::parse();

    // Build benchmark canister.
    assert!(Command::new("cargo")
        .args(["build", "--release", "--target", "wasm32-unknown-unknown"])
        .current_dir(
            PathBuf::new()
                .join(env::var("CARGO_MANIFEST_DIR").unwrap())
                .join("benchmark-canisters")
        )
        .status()
        .unwrap()
        .success());

    // Parse the Wasm to determine all the benchmarks to run.
    // All query endpoints are assumed to be benchmarks.
    let benchmark_canister_wasm = std::fs::read(
        PathBuf::new()
            .join(env::var("CARGO_MANIFEST_DIR").unwrap())
            .join("target")
            .join("wasm32-unknown-unknown")
            .join("release")
            .join("benchmarks.wasm"),
    )
    .unwrap();

    let benchmark_fns: Vec<_> = WasmParser::new(0)
        .parse_all(&benchmark_canister_wasm)
        .filter_map(|section| match section {
            Ok(wasmparser::Payload::ExportSection(export_section)) => {
                let queries: Vec<_> = export_section
                    .into_iter()
                    .filter_map(|export| {
                        if let Ok(export) = export {
                            if export.name.starts_with("canister_query ") {
                                return Some(
                                    export
                                        .name
                                        .split_whitespace()
                                        .last()
                                        .expect("query must have name."),
                                );
                            }
                        }

                        return None;
                    })
                    .collect();

                Some(queries)
            }
            _ => None,
        })
        .flatten()
        .collect();

    let current_results = read_current_results();

    let mut results = BTreeMap::new();

    for bench_fn in benchmark_fns {
        if let Some(pattern) = &args.pattern {
            if !bench_fn.contains(pattern) {
                continue;
            }
        }

        println!();
        println!("---------------------------------------------------");
        println!();

        let output = Command::new("bash")
            .current_dir(benchmarks_dir())
            .args(vec!["run-benchmark.sh", bench_fn])
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            output.status.success(),
            "executing benchmark failed: {stdout}\n{stderr}"
        );

        let result = Decode!(&hex::decode(stdout.trim()).unwrap(), BenchResult).unwrap();

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
    if args.persist {
        // Open a file in write-only mode, returns `io::Result<File>`
        let mut file = File::create(benchmarks_dir().join(RESULTS_FILE)).unwrap();
        file.write_all(serde_yaml::to_string(&results).unwrap().as_bytes())
            .unwrap();
        println!("Successfully persisted results to {}", RESULTS_FILE);
    }
}
