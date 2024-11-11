<p>
  <a href="https://crates.io/crates/ic-stable-structures"><img alt="Crate Info" src="https://img.shields.io/crates/v/ic-stable-structures.svg"/></a>
  <a href="https://github.com/dfinity/stable-structures/blob/master/LICENSE"><img alt="Apache-2.0" src="https://img.shields.io/github/license/dfinity/stable-structures"/></a>
  <a href="https://docs.rs/ic-stable-structures"><img alt="API Docs" src="https://img.shields.io/badge/docs.rs-ic--stable--structures-blue"/></a>
  <a href="https://forum.dfinity.org/"><img alt="Chat on the Forum" src="https://img.shields.io/badge/help-post%20on%20forum.dfinity.org-blue"></a>
</p>

# Stable Structures

A collection of scalable data structures for the [Internet Computer](https://internetcomputer.org) that persist across upgrades.

Stable structures are designed to use stable memory as the backing store, allowing them to grow to gigabytes in size without the need for `pre_upgrade`/`post_upgrade` hooks.

## Background

The conventional approach to canister state persistence is to serialize the entire state to stable memory in the `pre_upgrade` hook and decode it back in the `post_upgrade` hook.
This approach is easy to implement and works well for relatively small datasets.
Unfortunately, it does not scale well and can render a canister non-upgradable.

This library aims to simplify managing data structures directly in stable memory.
For more information about the philosophy behind the library, see [Roman's tutorial on stable structures](https://mmapped.blog/posts/14-stable-structures.html).

## Available Data Structures

- [BTreeMap]: A Key-Value store
- [Vec]: A growable array
- [Log]: An append-only list of variable-size entries
- [Cell]: A serializable value
- [MinHeap]: A priority queue.

## Tutorials

[Schema Upgrades](./docs/schema-upgrades.md)

## How it Works

Stable structures are able to work directly in stable memory because each data structure manages
its own memory.
When initializing a stable structure, a memory is provided that the data structure can use to store its data.

Here's a basic example:

```rust
use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
let mut map: BTreeMap<u64, u64, _> = BTreeMap::init(DefaultMemoryImpl::default());

map.insert(1, 2);
assert_eq!(map.get(&1), Some(2));
```

Memories are abstracted with the [Memory] trait, and stable structures can work with any storage
backend that implements this trait.
This includes stable memory, a vector ([VectorMemory]), or even a flat file ([FileMemory]).

The example above initializes a [BTreeMap] with a [DefaultMemoryImpl], which maps to stable memory when used in a canister and to a [VectorMemory] otherwise.


Note that **stable structures cannot share memories.**
Each memory must belong to only one stable structure.
For example, this fails when run in a canister:


```no_run
use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
let mut map_1: BTreeMap<u64, u64, _> = BTreeMap::init(DefaultMemoryImpl::default());
let mut map_2: BTreeMap<u64, u64, _> = BTreeMap::init(DefaultMemoryImpl::default());

map_1.insert(1, 2);
map_2.insert(1, 3);
assert_eq!(map_1.get(&1), Some(2)); // This assertion fails.
```

It fails because both `map_1` and `map_2` are using the same stable memory under the hood, and so changes in `map_1` end up changing or corrupting `map_2`.

To address this issue, we make use of the [MemoryManager](memory_manager::MemoryManager), which takes a single memory and creates up to 255 virtual memories for our disposal.
Here's the above failing example, but fixed by using the [MemoryManager](memory_manager::MemoryManager):

```rust
use ic_stable_structures::{
   memory_manager::{MemoryId, MemoryManager},
   BTreeMap, DefaultMemoryImpl,
};
let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
let mut map_1: BTreeMap<u64, u64, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(0)));
let mut map_2: BTreeMap<u64, u64, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(1)));

map_1.insert(1, 2);
map_2.insert(1, 3);
assert_eq!(map_1.get(&1), Some(2)); // Succeeds, as expected.
```

## Example Canister

Here's a fully working canister example that ties everything together.

Dependencies:

```toml
[dependencies]
ic-cdk = "0.6.8"
ic-cdk-macros = "0.6.8"
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
    static MAP: RefCell<StableBTreeMap<u128, u128, Memory>> = RefCell::new(
        StableBTreeMap::init(
            MEMORY_MANAGER.with(|m| m.borrow().get(MemoryId::new(0))),
        )
    );
}

// Retrieves the value associated with the given key if it exists.
#[ic_cdk_macros::query]
fn get(key: u128) -> Option<u128> {
    MAP.with(|p| p.borrow().get(&key))
}

// Inserts an entry into the map and returns the previous value of the key if it exists.
#[ic_cdk_macros::update]
fn insert(key: u128, value: u128) -> Option<u128> {
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