//! A script for running benchmarks on a canister.
//! To run this script, run `cargo bench`.
use clap::Parser;
use profiler::benchmark::run_benchmarks;
use std::{env, path::PathBuf};

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

fn main() {
    let args = Args::parse();

    run_benchmarks(
        PathBuf::new()
            .join(env::var("CARGO_MANIFEST_DIR").unwrap())
            .join("benchmark-canisters"),
        PathBuf::new()
            .join(env::var("CARGO_MANIFEST_DIR").unwrap())
            .join("target")
            .join("wasm32-unknown-unknown")
            .join("release")
            .join("benchmarks.wasm"),
        args.pattern,
        args.persist,
        PathBuf::new()
            .join(env::var("CARGO_MANIFEST_DIR").unwrap())
            .join("benchmarks")
            .join("results.yml"),
    );
}
