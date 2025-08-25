# Memory Manager

As mentioned in the previous section, each stable structure requires its own dedicated `Memory` instance.
This is an intentional design decision that limits [the blast radius](../introduction/design-principles.md) of potential bugs, ensuring that issues only affect the specific stable structure and its associated memory, not other stable structures.

## Overview

The Memory Manager enables the creation of up to 255 virtual memories from a single underlying memory instance.
When used with stable memory, this allows you to maintain up to 255 separate stable structures, each with its own isolated memory space.

## Usage Example

The following example demonstrates how to use the Memory Manager to create multiple stable structures:

```rust
use ic_stable_structures::{
   memory_manager::{MemoryId, MemoryManager},
   BTreeMap, DefaultMemoryImpl,
};

// Initialize a MemoryManager with DefaultMemoryImpl as the underlying memory
let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());

// Create two separate BTreeMaps, each with its own virtual memory
let mut map_1: BTreeMap<u64, u64, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(0)));
let mut map_2: BTreeMap<u64, u64, _> = BTreeMap::init(mem_mgr.get(MemoryId::new(1)));

// Demonstrate independent operation of the two maps
map_1.insert(1, 2);
map_2.insert(1, 3);
assert_eq!(map_1.get(&1), Some(2)); // Succeeds as expected
```

```admonish warning ""
Virtual memories from the `MemoryManager` cannot be shared between stable structures.
Each memory instance should be assigned to exactly one stable structure.
```
