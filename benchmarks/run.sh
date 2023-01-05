#!/usr/bin/env bash
set -Eexuo pipefail

# Move to the script directory.
SCRIPT_DIR=$(cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)
pushd "$SCRIPT_DIR"

# Run dfx stop if we run into errors.
trap "dfx stop" ERR EXIT

# Run dfx and deploy the benchmarks canister.
dfx start --background --clean
dfx deploy --no-wallet benchmarks

# BTreeMap benchmarks
dfx canister call benchmarks btreemap_insert --query
dfx canister call benchmarks btreemap_remove --query

# MemoryManager benchmarks
dfx canister call benchmarks memory_manager_baseline --query
dfx canister call benchmarks memory_manager_interleaved "(64:nat16)" --query
dfx canister call benchmarks memory_manager_interleaved "(128:nat16)" --query
dfx canister call benchmarks memory_manager_interleaved "(512:nat16)" --query
dfx canister call benchmarks memory_manager_interleaved "(1024:nat16)" --query
dfx canister call benchmarks memory_manager_interleaved "(2048:nat16)" --query
