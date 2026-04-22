# Stable Structures Deep Dive

This document is for contributors who want to work on the `stable-structures` library itself. It covers the design reasoning, internal architecture, and implementation patterns that are not visible from the public API — the kind of context you need before making a meaningful change. It is not a usage guide; for that, see the [README](../../../README.md).

## Background and Motivation

The Internet Computer (IC) runs canister smart contracts. When a canister is upgraded, its heap is wiped. The conventional fix is to serialize all state to stable memory in a `pre_upgrade` hook and deserialize it in `post_upgrade`. This works for small state but does not scale: the serialization itself costs cycles, and a bug in either hook can make the canister permanently non-upgradable.

`stable-structures` eliminates both problems by keeping data structures permanently resident in stable memory. There is nothing to serialize on upgrade and no upgrade hooks to write.

[Design principles](./design-principles.md) baked into every structure:

- **Radical simplicity** — the simplest design that solves the problem
- **Backward compatibility** — every header starts with a magic string and a layout version, so new library versions can always read old data
- **No `pre_upgrade` hooks** — structures must not require migration on upgrade
- **Limited blast radius** — a bug in one structure cannot corrupt another
- **No reallocation** — moving data in bulk is too expensive in cycles; all growth happens in place
- **Multi-memory compatibility** — the design works with multiple stable memories, ensuring forward compatibility with upcoming IC features

The structures library ships:

| Structure       | Description                       | Container Type      | Memories needed  |
|-----------------|-----------------------------------|---------------------|------------------|
| `Cell`          | Single serializable value         | Bounded + Unbounded | 1                |
| `BTreeMap`      | Ordered key-value store           | Bounded + Unbounded | 1                |
| `BTreeSet`      | Ordered set of unique keys        | Bounded + Unbounded | 1                |
| `Vec`           | Growable array                    | Bounded only        | 1                |
| `Log`           | Append-only variable-size entries | Bounded + Unbounded | 2 (index + data) |
| `MinHeap`       | Priority queue                    | Bounded only        | 1                |
| `MemoryManager` | Manages on-demand virtual memory  | n/a                 | 1                |

## Core Abstractions

### The Memory Trait

The `Memory` trait is the decoupling layer at the heart of the library.
Every stable structure is generic over it, so any structure works unchanged with IC stable memory on-chain, `VectorMemory` in tests, or `FileMemory` locally — with no code changes to the structure itself (`src/lib.rs:52-93`).

The four methods deliberately mirror the WebAssembly linear memory API.
One thing is notably absent: there is no `free` or `shrink`. 
WebAssembly memory can only grow, and this constraint propagates through the entire library — every design decision around memory reuse traces back to it.

```rust
/// Abstraction over a WebAssembly-style linear memory.
pub trait Memory {
    /// Returns the current size in pages (1 page = 64 KiB).
    fn size(&self) -> u64;

    /// Grows by pages, returns the previous size, or -1 on failure.
    fn grow(&self, pages: u64) -> i64;

    /// Reads bytes.
    fn read(&self, offset: u64, dst: &mut [u8]);

    /// Writes bytes.
    fn write(&self, offset: u64, src: &[u8]);
}
```

Concrete implementations:

- `Ic0StableMemory` — wraps the IC system API, only compiled for `wasm32`
- `VectorMemory` — a `Vec<u8>` in heap, used in tests and locally
- `FileMemory` — file-backed memory using standard file I/O, useful for offline development and persistence
- `DefaultMemoryImpl` — resolves to `Ic0StableMemory` in `wasm32`, `VectorMemory` otherwise

`RestrictedMemory` (`src/lib.rs:243-308`) is a public `Memory` adapter that exposes a fixed page range of a larger memory as its own address space starting at 0. It is the simpler alternative to `MemoryManager` for cases where each structure's maximum size is known upfront — covered in the MemoryManager section below.

### The Storable Trait

Stable structures are generic and work only with raw bytes — they have no knowledge of the types stored in them. `Storable` (`src/storable.rs:13-72`) is the bridge: it tells a structure how to convert a value to and from bytes. Any type you want to store must implement it. The library already provides implementations for the most common types; custom types require a manual implementation:

```rust
pub trait Storable {
    fn to_bytes(&self) -> Cow<'_, [u8]>;
    fn into_bytes(self) -> Vec<u8>;
    fn from_bytes(bytes: Cow<[u8]>) -> Self;
    const BOUND: Bound;
}
```

The two serialization methods serve different call sites:

- **`to_bytes`** is for reads — it borrows `self` and can return `Cow::Borrowed`, a zero-copy slice, which is ideal for lookups and iteration.
- **`into_bytes`** is for writes — `insert` must own the value's bytes as they travel through the tree and get stored in a node. For types like `Vec<u8>` or `String` whose serialized form *is* their internal buffer, `to_bytes` would return `Cow::Borrowed`, and calling `.into_owned()` on that always clones. `into_bytes(self)` moves the buffer directly instead — no allocation. For types with no owned buffer to move (primitives, fixed-size structs), the correct fallback is simply `self.to_bytes().into_owned()`.

The extra required method adds one line of boilerplate for each `Storable` impl, but eliminates a guaranteed heap allocation on every `insert` for the most common value types.

The `BOUND` constant is the key design decision a user must make:

- **`Bound::Unbounded`** — no size constraints; the structure stores a length prefix before each value. Safest default for types with `String`s or `Vec`s.
- **`Bound::Bounded { max_size: u32, is_fixed_size: bool }`** — `max_size` is enforced at runtime via `to_bytes_checked()`. Setting `is_fixed_size: true` eliminates the length prefix, saving bytes per entry. **You cannot increase `max_size` after deployment without corrupting data.**

The library ships `Storable` implementations for all primitives (`u8` through `u128`, `f32`/`f64`, `bool`), `[u8; N]`, `Blob<N>` (a fixed-size byte array wrapper type), `String`, `Vec<u8>`, `Principal`, `Option<T>`, and tuples.

Note: `Storable` says nothing about the serialization format. Users commonly use CBOR (`ciborium`), protobuf, or Candid inside `to_bytes`/`from_bytes`. See `docs/src/schema-upgrades.md` for patterns for adding fields safely.

### The MemoryManager

Each stable structure requires exclusive ownership of its memory — sharing causes corruption. The naive alternative, carving stable memory into static regions via `RestrictedMemory`, has two problems: you must know the size limit upfront, and the full region is paid for even when mostly empty.

`MemoryManager` eliminates both problems. It presents each structure with a `VirtualMemory` that has no upfront size limit and grows on demand. Underneath, it divides the real stable memory into 128-page buckets allocated as needed and interleaved freely across virtual memories — so total stable memory usage stays proportional to actual data, not declared limits.

```
1) NAIVE (RestrictedMemory)
   limits declared upfront, full region allocated immediately

  Stable memory
  ┌──────────────────────────────┬──────────────────────────────┐
  │  RestrictedMemory 0 (fixed)  │  RestrictedMemory 1 (fixed)  │
  │  ▓▓▓░░░░░░░░░░░░░░░░░░░░░░░  │  ▓▓░░░░░░░░░░░░░░░░░░░░░░░░  │
  │  ~15% used, rest wasted      │  ~10% used, rest wasted      │
  └──────────────────────────────┴──────────────────────────────┘

2) WITH MemoryManager — no limits, buckets allocated on demand

  VirtualMemory 0  [▓▓▓▓]    ▓ = VM0 bucket
  VirtualMemory 1  [▒▒]      ▒ = VM1 bucket
        ▼
  Stable memory
  ▓▓▒▒▓▓▓▓▒▒▓▓·······················
  └──────────────┘└───────────────────
    interleaved        unallocated
```

The first page of the real memory holds the manager's own header:

```
magic "MGR" + version          ↕ 4 bytes
number of allocated buckets    ↕ 2 bytes
bucket size in pages           ↕ 2 bytes
per-memory page counts         ↕ 255 × 8 bytes
bucket ownership table         ↕ 1 byte per bucket (value = MemoryId)
```

Each `VirtualMemory` is identified by a `MemoryId` (a `u8`, up to 255 supported) — a stable, persistent handle that always refers to the same virtual memory across upgrades. Call `memory_manager.get(MemoryId::new(n))` to obtain one and pass it to a stable structure.

Each `VirtualMemory` presents a contiguous address space even though its physical buckets can be scattered. A read/write call translates logical page offsets through the bucket table to absolute pages in the underlying memory.

Usage pattern every canister should follow:

```rust
thread_local! {
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> = RefCell::new(
        MemoryManager::init(DefaultMemoryImpl::default())
    );

    static MAP: RefCell<StableBTreeMap<K, V, Memory>> = RefCell::new(
        StableBTreeMap::init(
            MEMORY_MANAGER.with(|m| m.borrow().get(MemoryId::new(0)))
        )
    );
}
```

See `examples/src/basic_example/src/lib.rs` for the minimal working canister.

### Internal Allocators

Memory allocation is invisible to users of stable-structures — structures interact only through the `Memory` trait and have no way to express "free this region." It is only relevant when working on the internals of a specific structure, where the choice of allocation strategy directly shapes the implementation.

The key question that drives each structure's strategy: can holes appear in its memory?

#### No allocator: direct memory access

**`Cell`** stores a single value and accepts both bounded and unbounded types. There is only ever one value — when it changes, the old bytes are overwritten in-place. No slots, no holes, no allocator needed; the structure reads and writes directly to its memory.

**`Log`** also accepts both bounded and unbounded types. It is strictly append-only: entries are written sequentially and nothing can be modified or removed. Holes are structurally impossible, so no allocator is needed. (Log uses two memories — one for the index of byte offsets, one for the data — which is why it requires two `MemoryId`s from the `MemoryManager`.)

#### No allocator: fixed-size slots

**`Vec`** and **`MinHeap`** are currently bounded-only. With a fixed `max_size`, every element occupies an equal-size slot at a predictable offset (`DATA_OFFSET + i * SLOT_SIZE`), and all mutations happen at the tail — pushes append, pops shrink, overwrites replace in-place. No holes, no allocator needed. Supporting unbounded types would require variable-size entries, which breaks fixed offsets: you could no longer find element `i` without scanning all prior entries. Tracking positions would require an index similar to `Log`, and reclaiming space after a removal would require a custom allocator — so unbounded `Vec` is a significantly more complex structure.

#### Custom allocator: free-list

**`BTreeMap`** requires a custom allocator regardless of whether bounded or unbounded types are used (V1, which is bounded-only, has it too). The reason is that B-tree rebalancing — splits, merges, and deletes — frees nodes at **arbitrary positions** throughout the memory. These holes must be tracked and reused. `BTreeMap` handles this with an internal free-list chunk allocator at `src/btreemap/allocator.rs`, located at a fixed offset inside the BTreeMap's memory right after its header.

The allocator divides remaining memory into equal-size chunks. Free chunks form a singly-linked list: allocation pops the head, deallocation pushes back onto it — both O(1). When the free list is empty, the memory grows and a new chunk is appended.


## Lifecycle, Schema Upgrades, and Migrations

### Lifecycle Across Upgrades

Every stable structure has two constructors:

- `new(memory)` — writes a fresh magic header and initialises an empty structure
- `init(memory)` — checks for the magic header; loads the existing structure if found, creates a new one otherwise

Always use `init` in a canister. Because stable memory survives upgrades, calling `init` on next deployment finds the existing data and resumes from it — no `pre_upgrade`/`post_upgrade` needed. The magic header also carries a layout version, so new library versions can always read data written by older ones.

### Layout Versioning: BTreeMap V1 → V2

`BTreeMap` is currently the only structure that has shipped two layout versions. Each version uses "node pages" — the fixed-size byte buffers the internal allocator assigns to each B-tree node (distinct from Wasm pages and MemoryManager buckets):

- **V1** supports only `Bound::Bounded` types. The node page size is derived at load time from `max_key_size` and `max_value_size` stored in the header, so it is implicit rather than stored explicitly.
- **V2** adds support for `Bound::Unbounded` types by storing the node page size explicitly in the header and introducing overflow pages — when a node's data exceeds one page, it chains additional pages.

Migration from V1 to V2 is **transparent and non-breaking**: calling `BTreeMap::init()` on an existing V1 map automatically upgrades it to V2 on first load — existing data is preserved, no user action required. Any unrecognized layout version causes a panic at startup.

### Schema Upgrades

Stable structures don't enforce a serialization format. The recommended pattern for evolving types is to use a flexible format (e.g. CBOR via `ciborium`) and `Bound::Unbounded`:

```rust
impl Storable for Asset {
    fn to_bytes(&self) -> Cow<'_, [u8]> { /* CBOR encode */ }
    fn into_bytes(self) -> Vec<u8>      { /* CBOR encode */ }
    fn from_bytes(bytes: Cow<[u8]>) -> Self { /* CBOR decode */ }
    const BOUND: Bound = Bound::Unbounded;
}
```

Adding a field is then safe with `#[serde(default)]` — old records decode without error and the new field gets its default. For fields with no sensible default, use `Option`. See `docs/src/schema-upgrades.md` for worked examples.

**Warning:** if you used `Bound::Bounded`, never increase `max_size` after deployment — existing node pages were sized to the old value and enlarging it corrupts them. Migrating from `Bounded` to `Unbounded` is safe; the reverse is not.

### Data Migrations

When an in-place field addition isn't enough — e.g. changing the key type or restructuring the value layout entirely — data must be migrated from one structure to another.

For anything beyond a trivial dataset, migration cannot happen in a single upgrade call. The IC enforces a per-round instruction limit, so even a moderately large structure will trap if you try to read-transform-write it all at once.

The practical approach is to run the migration incrementally across many canister update calls:

1. Create the new structure under a fresh `MemoryId` alongside the old one.
2. Each update call migrates a small batch of records from old to new, tracking progress in a version field or migration cursor.
3. During migration, both structures are live. A routing layer directs reads and writes to whichever structure owns each record — unmigrated records go to the old structure, already-migrated ones to the new.
4. Once all records are migrated, the routing layer is dropped and the old structure is cleared.

This is the pattern NNS-dapp used when migrating accounts to stable memory: two schemas active simultaneously, new writes applied to both during the transition, migration driven by a periodic job chunk by chunk.

The cost to be aware of: both structures occupy stable memory simultaneously (~2× peak usage), and after the old structure is cleared its buckets remain permanently assigned to its `MemoryId` — they cannot be reclaimed or reused. Budget for this when planning large schema changes.

### MemoryManager Limitations and Bucket Reclamation

The inability to reuse freed buckets is a known limitation rooted in a structural invariant of the current MemoryManager: **buckets within each virtual memory must be stored in ascending order by ID**. Because the header encodes only the owning `MemoryId` per bucket (1 byte), there is no room to store an explicit ordering — the order is implied by bucket position. To load a virtual memory correctly, the runtime simply scans for all buckets belonging to that `MemoryId` and traverses them in ID order.

This makes safe reuse impossible in the typical migration layout. When structure A occupies buckets 0–99 and is cleared, structure B (buckets 100–199) cannot absorb A's freed buckets — they have lower IDs than B's current maximum, so inserting them would violate the ascending invariant and corrupt B's data on the next load.

#### Attempted fix: conservative bucket reuse

A partial fix, **conservative bucket reuse**, was implemented and then [reverted](https://github.com/dfinity/stable-structures/pull/396). It allowed reuse only of freed buckets with IDs *higher* than the growing virtual memory's current maximum — a constraint that is almost never satisfied in practice, since A allocates first and therefore always has lower IDs than B.

#### Alternative design: explicit linked list of buckets (not implemented)

The proper solution requires a new header layout. The alternative design replaces implicit ID ordering with an **explicit linked list**: each bucket stores a 4-byte pointer to the next bucket in its virtual memory's chain. Freeing a virtual memory then simply nulls out its head pointer, making all its buckets immediately available for any new allocation regardless of their IDs.

The redesign also removes the current 32,768-bucket cap (`MAX_NUM_BUCKETS`), raising it to 2^32 and lifting the effective stable memory ceiling from 256 GiB to well beyond current IC capacity.

The tradeoff: this is a **breaking change**. The on-disk header format is incompatible with the current layout, so existing canisters will need a one-time migration when the new MemoryManager ships.

## StableBTreeMap Internals

`StableBTreeMap` is the most commonly used structure in this library, and its design is a direct response to the IC's per-round instruction limits.

A hash map must rehash — copying all entries — when it grows, which is prohibitive at scale. A red-black tree avoids bulk copies but stores one key per node, so a lookup requires many scattered reads. A B-tree avoids both: it stores multiple keys per node in a single contiguous chunk, so each read fetches an entire node at once, and growth allocates exactly one new node at a time.

The remaining challenge is fragmentation: B-tree splits, merges, and deletes free nodes at arbitrary positions, leaving holes. The internal free-list allocator reclaims those holes immediately, so stable memory stays compact and every byte is either actively used or available for the next allocation.

### How BTreeMap Works

A `BTreeMap` is a tree of fixed-size nodes, each holding up to 11 key-value entries sorted by key. Lookups and inserts walk from the root down to a leaf, binary-searching within each node. Splits and merges keep the tree balanced.

Each node is stored as a contiguous byte chunk allocated by the internal free-list allocator. Only the nodes touched by an operation are read or written — the rest of the tree is never loaded.

### Performance-Critical Design Decisions

Because every read and write costs instructions, several optimizations keep the per-operation cost low:

**Lazy key and value loading** (`src/btreemap/node.rs`) — each entry holds a `LazyObject`: either an already-decoded value or an `(offset, size)` reference into the node's raw bytes, resolved on first access via `OnceCell`. Values are always deferred — they are never touched during a tree traversal.

For keys, the strategy depends on size: keys ≤ 16 bytes are decoded eagerly on node load (cheaper than storing a reference for tiny payloads), while larger keys are kept as byte references and decoded only when the binary search actually reaches them.

**Zero-copy writes** — `insert` calls `into_bytes()` rather than `to_bytes()`, moving the value's buffer directly into the write path for types like `Vec<u8>` and `String` with no extra allocation. (See the Storable Trait section for why the trait has both methods.)

**Lazy range iteration** (`src/btreemap/iter.rs`) — the iterator advances one entry at a time. Values are only decoded when the caller actually dereferences the iterator, so ranging over keys without touching values incurs no deserialization cost.

### Key Files

| File | Purpose |
|---|---|
| `src/btreemap.rs` | Public API, header, `init`/`insert`/`get`/`remove` |
| `src/btreemap/allocator.rs` | Free-list chunk allocator |
| `src/btreemap/node.rs` | In-memory `Node`, lazy entry loading |
| `src/btreemap/node/v1.rs` | Node serialization (old format) |
| `src/btreemap/node/v2.rs` | Node serialization (current format) |
| `src/btreemap/iter.rs` | Lazy range iteration |

## Contributor Development Loop

### Testing

```sh
cargo test
```

Tests fall into two categories:

**Unit tests** live inside each module and check specific behaviors. See `src/btreemap/node/tests.rs` as a model.

**Property-based tests** (`src/btreemap/proptests.rs`) use `proptest` to generate random sequences of inserts, removes, and gets, then verify results against `std::collections::BTreeMap`. This is the primary correctness check — if a stable structure diverges from the standard library equivalent under any sequence of operations, the test fails. Running `cargo test` covers both.

### Fuzzing (requires nightly)

```sh
cargo +nightly fuzz run stable_btreemap_multiple_ops_persistent
```

Fuzz targets in `fuzz/fuzz_targets/` run random operation sequences and check for crashes and invariant violations. The `_persistent` variants reuse a single structure across iterations, which is effective at finding bugs that only appear after accumulated state changes.

### Benchmarks and CI regression checks

Benchmarks measure **instruction counts**, not wall time — instructions are the actual cost unit on the IC. Benchmarks exist for all performance-critical structures (`benchmarks/btreemap`, `btreeset`, `vec`, `memory-manager`, `nns`, `io_chunks`).

```sh
cargo install canbench
cd benchmarks/btreemap && canbench
```

Every PR runs all benchmarks in CI and compares results against the `main` branch baseline. If any benchmark regresses or improves, **the CI job fails** until the results are explicitly acknowledged:

```sh
canbench --persist   # update canbench_results.yml with new baseline
```

This means `canbench_results.yml` in each benchmark directory is a committed, reviewed record of expected performance. Any change to a hot path must either stay within the existing baseline or ship with an updated `canbench_results.yml` that explains the change.
