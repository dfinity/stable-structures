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

// The file to persist benchmark results to.
const RESULTS_FILE: &str = "results.yml";

lazy_static::lazy_static! {
    // The benchmarks to run.
    static ref BENCHES: Vec<&'static str> = vec![
        // MemoryManager benchmarks
        "memory_manager_baseline",
        "memory_manager_overhead",
        "buckets_allocation",

        // BTree benchmarks
        "btreemap_insert_10mib_values",
        "btreemap_insert_blob_4_1024",
        "btreemap_insert_blob_4_1024_v2",
        "btreemap_insert_blob_8_1024",
        "btreemap_insert_blob_8_1024_v2",
        "btreemap_insert_blob_16_1024",
        "btreemap_insert_blob_16_1024_v2",
        "btreemap_insert_blob_32_1024",
        "btreemap_insert_blob_32_1024_v2",
        "btreemap_insert_blob_64_1024",
        "btreemap_insert_blob_64_1024_v2",
        "btreemap_insert_blob_128_1024",
        "btreemap_insert_blob_128_1024_v2",
        "btreemap_insert_blob_256_1024",
        "btreemap_insert_blob_256_1024_v2",
        "btreemap_insert_blob_512_1024",
        "btreemap_insert_blob_512_1024_v2",
        "btreemap_insert_u64_u64",
        "btreemap_insert_u64_u64_v2",
        "btreemap_insert_u64_blob_8",
        "btreemap_insert_u64_blob_8_v2",
        "btreemap_insert_blob_8_u64",
        "btreemap_insert_blob_8_u64_v2",

        "btreemap_get_blob_4_1024",
        "btreemap_get_blob_4_1024_v2",
        "btreemap_get_blob_8_1024",
        "btreemap_get_blob_8_1024_v2",
        "btreemap_get_blob_16_1024",
        "btreemap_get_blob_16_1024_v2",
        "btreemap_get_blob_32_1024",
        "btreemap_get_blob_32_1024_v2",
        "btreemap_get_blob_64_1024",
        "btreemap_get_blob_64_1024_v2",
        "btreemap_get_blob_128_1024",
        "btreemap_get_blob_128_1024_v2",
        "btreemap_get_u64_u64",
        "btreemap_get_u64_u64_v2",
        "btreemap_get_u64_blob_8",
        "btreemap_get_u64_blob_8_v2",
        "btreemap_get_blob_8_u64",
        "btreemap_get_blob_8_u64_v2",
        "btreemap_get_blob_256_1024",
        "btreemap_get_blob_256_1024_v2",
        "btreemap_get_blob_512_1024",
        "btreemap_get_blob_512_1024_v2",

        "btreemap_remove_blob_4_1024",
        "btreemap_remove_blob_4_1024_v2",
        "btreemap_remove_blob_8_1024",
        "btreemap_remove_blob_8_1024_v2",
        "btreemap_remove_blob_16_1024",
        "btreemap_remove_blob_16_1024_v2",
        "btreemap_remove_blob_32_1024",
        "btreemap_remove_blob_32_1024_v2",
        "btreemap_remove_blob_64_1024",
        "btreemap_remove_blob_64_1024_v2",
        "btreemap_remove_blob_128_1024",
        "btreemap_remove_blob_128_1024_v2",
        "btreemap_remove_blob_256_1024",
        "btreemap_remove_blob_256_1024_v2",
        "btreemap_remove_blob_512_1024",
        "btreemap_remove_blob_512_1024_v2",
        "btreemap_remove_u64_u64",
        "btreemap_remove_u64_u64_v2",
        "btreemap_remove_u64_blob_8",
        "btreemap_remove_u64_blob_8_v2",
        "btreemap_remove_blob_8_u64",
        "btreemap_remove_blob_8_u64_v2",

        // Vec benchmarks
        "vec_insert_blob_4",
        "vec_insert_blob_8",
        "vec_insert_blob_16",
        "vec_insert_blob_32",
        "vec_insert_blob_128",
        "vec_insert_u64",

        "vec_get_blob_4",
        "vec_get_blob_8",
        "vec_get_blob_16",
        "vec_get_blob_32",
        "vec_get_blob_128",
        "vec_get_u64",
    ];
}

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

    let current_results = read_current_results();

    let mut results = BTreeMap::new();

    for bench_fn in BENCHES.iter() {
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

        results.insert(*bench_fn, result);
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
