<p>
  <a href="https://crates.io/crates/ic-stable-structures"><img alt="Crate Info" src="https://img.shields.io/crates/v/ic-stable-structures.svg"/></a>
  <a href="https://github.com/dfinity/stable-structures/blob/master/LICENSE"><img alt="Apache-2.0" src="https://img.shields.io/github/license/dfinity/stable-structures"/></a>
  <a href="https://docs.rs/ic-stable-structures"><img alt="API Docs" src="https://img.shields.io/badge/docs.rs-ic--stable--structures-blue"/></a>
  <a href="https://forum.dfinity.org/"><img alt="Chat on the Forum" src="https://img.shields.io/badge/help-post%20on%20forum.dfinity.org-blue"></a>
</p>

# Stable Structures

A collection of scalable data structures for the [Internet Computer](https://internetcomputer.org) that persist across upgrades.

Stable structures are designed to use stable memory as the backing store, allowing them to grow to gigabytes in size without the need for `pre_upgrade`/`post_upgrade` hooks.

You can read more about the library in the [Stable Structures Book](https://dfinity.github.io/stable-structures/)

## Background

The conventional approach to canister state persistence is to serialize the entire state to stable memory in the `pre_upgrade` hook and decode it back in the `post_upgrade` hook.
This approach is easy to implement and works well for relatively small datasets.
Unfortunately, it does not scale well and can render a canister non-upgradable.

This library aims to simplify managing data structures directly in stable memory.

## Available Data Structures

- [Cell]: A serializable value
- [BTreeMap]: A Key-Value store
- [BTreeSet]: A set of unique elements
- [Vec]: A growable array
- [Log]: An append-only list of variable-size entries
- [MinHeap]: A priority queue.

## Tutorials

[Schema Upgrades](./docs/src/schema-upgrades.md)

## How it Works

Stable structures are able to work directly in stable memory because each data structure manages
its own memory.
When initializing a stable structure, a memory is provided that the data structure can use to store its data.

### Basic Usage

Here's a basic example:

```rust
use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
let mut map: BTreeMap<u64, String, _> = BTreeMap::init(DefaultMemoryImpl::default());

map.insert(1, "hello".to_string());
assert_eq!(map.get(&1), Some("hello".to_string()));
```

Memories are abstracted with the [Memory] trait, and stable structures can work with any storage
backend that implements this trait.
This includes stable memory, a vector ([VectorMemory]), or even a flat file ([FileMemory]).

The example above initializes a [BTreeMap] with a [DefaultMemoryImpl], which maps to stable memory when used in a canister and to a [VectorMemory] otherwise.

### Memory Isolation Requirement

> **⚠️ CRITICAL:** Stable structures **MUST NOT** share memories!
> Each memory must belong to only one stable structure.

For example, this fails when run in a canister:

```rust,ignore
use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(DefaultMemoryImpl::default());
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::init(DefaultMemoryImpl::default());

map_a.insert(1, b'A');
map_b.insert(1, b'B');
assert_eq!(map_a.get(&1), Some(b'A')); // ❌ FAILS: Returns b'B' due to shared memory!
assert_eq!(map_b.get(&1), Some(b'B')); // ✅ Succeeds, but corrupted map_a
```

It fails because both `map_a` and `map_b` are using the same stable memory under the hood, and so changes in `map_b` end up changing or corrupting `map_a`.

### Using MemoryManager

To address this issue, we use the [MemoryManager](memory_manager::MemoryManager), which takes a single memory and creates up to 255 virtual memories for our use.
Here's the above failing example, but fixed:

```rust
use ic_stable_structures::{
   memory_manager::{MemoryId, MemoryManager},
   BTreeMap, DefaultMemoryImpl,
};
let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
let (mem_id_a, mem_id_b) = (MemoryId::new(0), MemoryId::new(1));
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(mem_id_a));
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(mem_id_b));

map_a.insert(1, b'A');
map_b.insert(1, b'B');
assert_eq!(map_a.get(&1), Some(b'A')); // ✅ Succeeds: Each map has its own memory
assert_eq!(map_b.get(&1), Some(b'B')); // ✅ Succeeds: No data corruption
```

### Memory Reclamation

During migrations you often create a new structure (B) and copy data from an existing one (A). Without reclamation, this can double memory usage even after A is no longer needed.

Bucket IDs are an internal implementation detail — hidden and not user-controllable — and each virtual memory must receive bucket IDs in strictly ascending order. Because of this, reuse of freed buckets is guaranteed when allocating into a newly created (empty) structure. For existing structures, reuse may or may not work: it succeeds only if there is a free bucket with an ID greater than the structure’s current maximum; otherwise a new bucket is allocated.

Example: A = `[0, 4, 5]`, B = `[1, 2, 3]`. After releasing A, `free = [0, 4, 5]`. When B grows, it can’t take `0` (must be `> 3`) but can take `4` → `B = [1, 2, 3, 4]`, `free = [0, 5]`.

**Recommendation:** for predictable reuse migrate into a newly created structure rather than relying on reuse with a populated one.

> **⚠️ CRITICAL SAFETY REQUIREMENT:**
> - **MUST** drop the original structure object before calling `reclaim_memory`.
> - **NEVER** use the original structure after reclamation — doing so corrupts data.

The `MemoryManager` provides a `reclaim_memory` method to efficiently handle these scenarios:

```rust
use ic_stable_structures::{
    memory_manager::{MemoryId, MemoryManager},
    BTreeMap, DefaultMemoryImpl, Memory,
};

let mem = DefaultMemoryImpl::default();
let mem_mgr = MemoryManager::init(mem.clone());
let (mem_id_a, mem_id_b) = (MemoryId::new(0), MemoryId::new(1));

// ========================================
// Scenario 1: WITHOUT reclamation
// ========================================
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(mem_id_a));
map_a.insert(1, b'A');              // Populate map A with data
let data = map_a.get(&1);           // Extract data for migration
map_a.clear_new();                  // A is now empty
drop(map_a);                        // Memory stays allocated to mem_id_a
let actual_size_before_migration = mem.size();

let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::new(mem_mgr.get(mem_id_b));
map_b.insert(1, data.unwrap());     // B allocates NEW memory
let actual_size_after_migration = mem.size();
                                    // Result: ~2x memory usage
                                    // Memory allocation grew (waste)
assert!(actual_size_before_migration < actual_size_after_migration);

// ========================================
// Scenario 2: WITH reclamation
// ========================================
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(mem_id_a));
map_a.insert(1, b'A');              // Populate map A with data
let data = map_a.get(&1);           // Extract data for migration
map_a.clear_new();                  // A is now empty
drop(map_a);                        // Drop A completely
let actual_size_before_migration = mem.size();
mem_mgr.reclaim_memory(mem_id_a);   // Free A's memory buckets for reuse

// Reusing free memory buckets works best on newly created structures
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::new(mem_mgr.get(mem_id_b));
map_b.insert(1, data.unwrap());     // B reuses A's reclaimed memory buckets
let actual_size_after_migration = mem.size();
                                    // Result: 1x memory usage
                                    // Memory allocation stayed the same (no waste)
assert!(actual_size_before_migration == actual_size_after_migration);
```

## Example Canister

Here's a fully working canister example that ties everything together.

Dependencies:

```toml
[dependencies]
ic-cdk = "0.18.3"
ic-cdk-macros = "0.18.3"
ic-stable-structures = "0.7.1"
```

Code:

```rust
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager, VirtualMemory};
use ic_stable_structures::{DefaultMemoryImpl, StableBTreeMap};
use std::cell::RefCell;

type Memory = VirtualMemory<DefaultMemoryImpl>;

thread_local! {
    // The memory manager is used for simulating multiple memories. Given a `MemoryId` it can
    // return a memory that can be used by stable structures.
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));

    // Initialize a `StableBTreeMap` with `MemoryId(0)`.
    static MAP: RefCell<StableBTreeMap<u64, String, Memory>> = RefCell::new(
        StableBTreeMap::init(
            MEMORY_MANAGER.with(|m| m.borrow().get(MemoryId::new(0))),
        )
    );
}

// Retrieves the value associated with the given key if it exists.
#[ic_cdk_macros::query]
fn get(key: u64) -> Option<String> {
    MAP.with(|p| p.borrow().get(&key))
}

// Inserts an entry into the map and returns the previous value of the key if it exists.
#[ic_cdk_macros::update]
fn insert(key: u64, value: String) -> Option<String> {
    MAP.with(|p| p.borrow_mut().insert(key, value))
}
```

### More Examples

- [Basic Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/basic_example): Simple usage patterns
- [Quickstart Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/quick_start): Ideal as a template when developing a new canister
- [Custom Types Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/custom_types_example): Showcases storing your own custom types

## Combined Persistence

If your project uses only stable structures, memory can expand in size without requiring `pre_upgrade`/`post_upgrade` hooks.

However, if you also need to serialize/deserialize heap data, you must use the memory manager to avoid conflicts. To combine both approaches effectively, refer to the [Quickstart Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/quick_start) for guidance.

## Fuzzing

Stable structures require strong guarantees to work reliably and scale over millions of operations. To that extent, we use fuzzing to emulate such operations on the available data structures.

To run a fuzzer locally, 
```sh
rustup toolchain install nightly
cargo install cargo-fuzz

# To list available fuzzer targets
cargo +nightly fuzz list

# To run a target 
cargo +nightly fuzz run <TARGET_NAME>
```
