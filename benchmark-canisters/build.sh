#!/usr/bin/env bash
set -Eexuo pipefail

# Move to the script directory.
SCRIPT_DIR=$(cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)
pushd "$SCRIPT_DIR"

cargo build --release --target wasm32-unknown-unknown
gzip -n -f ./target/wasm32-unknown-unknown/release/benchmarks.wasm
