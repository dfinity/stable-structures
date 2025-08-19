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

Here are some basic examples:

### Example: BTreeMap

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

Note that **stable structures cannot share memories.**
Each memory must belong to only one stable structure.
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

It fails because both `map_a` and `map_b` are using the same stable memory under the hood, and so changes in `map_a` end up changing or corrupting `map_b`.

To address this issue, we make use of the [MemoryManager](memory_manager::MemoryManager), which takes a single memory and creates up to 255 virtual memories for our disposal.
Here's the above failing example, but fixed by using the [MemoryManager](memory_manager::MemoryManager):

```rust
use ic_stable_structures::{
   memory_manager::{MemoryId, MemoryManager},
   BTreeMap, DefaultMemoryImpl,
};
let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(0)));
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(1)));

map_a.insert(1, b'A');
map_b.insert(1, b'B');
assert_eq!(map_a.get(&1), Some(b'A')); // ✅ Succeeds: Each map has its own memory
assert_eq!(map_b.get(&1), Some(b'B')); // ✅ Succeeds: No data corruption
```

### Memory Reclamation

Virtual memories remain assigned to their memory IDs even after the data structure is dropped. This can cause memory waste during data migration scenarios. For example, when migrating from structure A to structure B using different memory IDs, the underlying memory grows 2x even though only one structure contains data.

**Without memory reclamation (memory waste):**
```rust
let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());

// Structure A uses memory
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(0)));
map_a.insert(1, b'A');

// Migrate data and create structure B with different ID
let data = map_a.get(&1);
drop(map_a); // A's memory remains allocated to ID 0
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(1))); // Allocates NEW memory
map_b.insert(1, data.unwrap());
// Result: 2x memory usage (A's unused memory + B's new memory)
```

**With memory reclamation (memory reuse):**
```rust
let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());

// Structure A uses memory
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(0)));
map_a.insert(1, b'A');

// Migrate data, drop structure, and reclaim memory
let data = map_a.get(&1);
drop(map_a);
mem_mgr.reclaim_memory(MemoryId::new(0)); // Free A's memory for reuse

// Structure B reuses A's memory
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(0))); // Reuses A's memory
map_b.insert(1, data.unwrap());
// Result: Same memory usage (B reuses A's memory)
```

**Important**: Always ensure the original structure is dropped before calling `reclaim_memory`.

## Example Canister

Here's a fully working canister example that ties everything together.

Dependencies:

```toml
[dependencies]
ic-cdk = "0.18.3"
ic-cdk-macros = "0.18.3"
ic-stable-structures = "0.5.6"
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

- [Basic Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/basic_example) (the one above)
- [Quickstart Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/quick_start): Ideal as a template when developing a new canister
- [Custom Types Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/custom_types_example): Showcases storing your own custom types

## Combined Persistence

If your project exclusively relies on stable structures, the memory can expand in size without the requirement of `pre_upgrade`/`post_upgrade` hooks.

However, it's important to note that if you also intend to perform serialization/deserialization of the heap data, utilizing the memory manager becomes necessary. To effectively combine both approaches, refer to the [Quickstart Example](https://github.com/dfinity/stable-structures/tree/main/examples/src/quick_start) for guidance.

## Fuzzing

Stable structures requires strong guarantees to work reliably and scale over millions of operations. To that extent, we use fuzzing to emulate such operations on the available data structures.

To run a fuzzer locally, 
```sh
rustup toolchain install nightly
cargo install cargo-fuzz

# To list available fuzzer targets
cargo +nightly fuzz list

# To run a target 
cargo +nightly fuzz run <TARGET_NAME>
```
