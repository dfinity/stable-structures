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
let (mem_id_a, mem_id_b) = (MemoryId::new(0), MemoryId::new(1));
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(mem_id_a));
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::init(mem_mgr.get(mem_id_b));

// Demonstrate independent operation of the two maps
map_a.insert(1, b'A');
map_b.insert(1, b'B');
assert_eq!(map_a.get(&1), Some(b'A')); // ✅ Succeeds: Each map has its own memory
assert_eq!(map_b.get(&1), Some(b'B')); // ✅ Succeeds: No data corruption
```

```admonish warning ""
**⚠️ CRITICAL:** Stable structures **MUST NOT** share memories!
Each memory instance must be assigned to exactly one stable structure.
```

## Memory Reclamation

During migrations you often create a new structure (B) and copy data from an existing one (A). Without reclamation, this can double memory usage even after A is no longer needed.

Bucket IDs are an internal implementation detail — hidden and not user-controllable — and each virtual memory must receive bucket IDs in strictly ascending order. Because of this, reuse of freed buckets is guaranteed when allocating into a newly created (empty) structure. For existing structures, reuse may or may not work: it succeeds only if there is a free bucket with an ID greater than the structure’s current maximum; otherwise a new bucket is allocated.

Example: A = `[0, 4, 5]`, B = `[1, 2, 3]`. After releasing A, `free = [0, 4, 5]`. When B grows, it can’t take `0` (must be `> 3`) but can take `4` → `B = [1, 2, 3, 4]`, `free = [0, 5]`.

**Recommendation:** for predictable reuse migrate into a newly created structure rather than relying on reuse with a populated one.

```admonish info ""
**⚠️ CRITICAL SAFETY REQUIREMENT:**
- **MUST** drop the original structure object before calling `reclaim_memory`.
- **NEVER** use the original structure after reclamation — doing so corrupts data.
```

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
