# The Memory Trait

Stable structures are responsible for managing their own memory.
To provide maximum flexibility, the library introduces the `Memory` trait:

```rust
pub trait Memory {
    /// Equivalent to WebAssembly memory.size.
    fn size(&self) -> u64;

    /// Equivalent to WebAssembly memory.grow.
    /// Returns the previous size, or -1 if the grow fails.
    fn grow(&self, pages: u64) -> i64;

    /// Copies bytes from this memory to the heap (in Wasm, memory 0).
    /// Panics or traps if out of bounds.
    fn read(&self, offset: u64, dst: &mut [u8]);

    /// Writes bytes from the heap (in Wasm, memory 0) to this memory.
    /// Panics or traps if out of bounds.
    fn write(&self, offset: u64, src: &[u8]);
}
```

The `Memory` trait intentionally models a [WebAssembly memory instance](https://webassembly.github.io/multi-memory/core/exec/runtime.html#memory-instances).
This design choice ensures consistency with the interface of memories available to canisters.
It also provides future compatibility with potential multi-memory support in canisters.

## Panics  

⚠️ `read` and `write` **assume the caller will not access memory outside the current size**.

If the range `[offset … offset + len)` exceeds available memory, the call panics (in native tests) or traps (in a Wasm canister).
Callers must store and check data lengths themselves or use higher-level containers such as `StableVec`.

## Available Memory Implementations

The library provides several implementations of the `Memory` trait, each designed for specific use cases:

- `Ic0StableMemory`: Stores data in the Internet Computer's stable memory
- `VectorMemory`: An in-memory implementation backed by a Rust `Vec<u8>`
- `DefaultMemoryImpl`: A smart implementation that automatically selects the appropriate memory backend:
  - Uses `Ic0StableMemory` when running in an Internet Computer canister (wasm32 target)
  - Falls back to `VectorMemory` in other environments (like tests or non-IC contexts)

Additional implementations such as `FileMemory` and `RestrictedMemory` exist but are less commonly used.

```admonish note ""
In most cases, you should use `DefaultMemoryImpl` as your memory implementation.
```

### Usage Example

Here's how to initialize a stable `BTreeMap` using `DefaultMemoryImpl`:

```rust
use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
let mut map: BTreeMap<u64, String, _> = BTreeMap::init(DefaultMemoryImpl::default());

map.insert(1, "hello".to_string());
assert_eq!(map.get(&1), Some("hello".to_string()));
```

```admonish warning ""
**⚠️ CRITICAL:** Stable structures **MUST NOT** share memories!
Each memory must belong to only one stable structure.
```

While the above example works correctly, it demonstrates a potential issue: the `BTreeMap` will use the entire stable memory.
This becomes problematic when trying to use multiple stable structures.
For example, the following code will fail in a canister:

```rust
use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
let mut map_a: BTreeMap<u64, u8, _> = BTreeMap::init(DefaultMemoryImpl::default());
let mut map_b: BTreeMap<u64, u8, _> = BTreeMap::init(DefaultMemoryImpl::default());

map_a.insert(1, b'A');
map_b.insert(1, b'B');
assert_eq!(map_a.get(&1), Some(b'A')); // ❌ FAILS: Returns b'B' due to shared memory!
assert_eq!(map_b.get(&1), Some(b'B')); // ✅ Succeeds, but corrupted map_a
```

The code fails because both `map_a` and `map_b` are using the same stable memory.
This causes changes in one map to affect or corrupt the other.

To solve this problem, the library provides the [MemoryManager](./memory-manager.md), which creates up to 255 virtual memories from a single memory instance.
We'll explore this solution in the next section.
