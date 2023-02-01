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

# MemoryManager benchmarks
dfx canister call benchmarks memory_manager_baseline --query
dfx canister call benchmarks memory_manager_overhead --query

# BTreeMap benchmarks
dfx canister call benchmarks btreemap_insert_blob_4_1024 --query
dfx canister call benchmarks btreemap_insert_blob_8_1024 --query
dfx canister call benchmarks btreemap_insert_blob_16_1024 --query
dfx canister call benchmarks btreemap_insert_blob_32_1024 --query
dfx canister call benchmarks btreemap_insert_blob_64_1024 --query
dfx canister call benchmarks btreemap_insert_blob_128_1024 --query

# These tests are called as update calls as they exceed the instruction limit
# for query calls.
dfx canister call benchmarks btreemap_insert_blob_256_1024
dfx canister call benchmarks btreemap_insert_blob_512_1024

dfx canister call benchmarks btreemap_get_blob_4_1024 --query
dfx canister call benchmarks btreemap_get_blob_8_1024 --query
dfx canister call benchmarks btreemap_get_blob_16_1024 --query
dfx canister call benchmarks btreemap_get_blob_32_1024 --query
dfx canister call benchmarks btreemap_get_blob_64_1024 --query
dfx canister call benchmarks btreemap_get_blob_128_1024 --query
# These tests go over the instruction limit, so we can't run them currently.
#dfx canister call benchmarks btreemap_get_blob_256_1024
#dfx canister call benchmarks btreemap_get_blob_512_1024

dfx canister call benchmarks btreemap_remove_blob_4_1024
dfx canister call benchmarks btreemap_remove_blob_8_1024
dfx canister call benchmarks btreemap_remove_blob_16_1024
dfx canister call benchmarks btreemap_remove_blob_32_1024
dfx canister call benchmarks btreemap_remove_blob_64_1024
dfx canister call benchmarks btreemap_remove_blob_128_1024
dfx canister call benchmarks btreemap_remove_blob_256_1024

# This test goes over the instructions limit, so we can't run it currently.
#dfx canister call benchmarks btreemap_remove_blob_512_1024
