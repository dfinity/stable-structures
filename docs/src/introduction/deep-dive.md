# Stable Structures Deep Dive

## Segment 1 — Why this library exists (10 min)

The Internet Computer (IC) runs canister smart contracts. When a canister is upgraded, its heap is wiped. The conventional fix is to serialize all state to stable memory in a `pre_upgrade` hook and deserialize it in `post_upgrade`. This works for small state but does not scale: the serialization itself costs cycles, and a bug in either hook can make the canister permanently non-upgradable.

`stable-structures` eliminates both problems by keeping data structures permanently resident in stable memory. There is nothing to serialize on upgrade and no upgrade hooks to write.

[Design principles](./design-principles.md) baked into every structure:

- **Radical simplicity** — the simplest design that solves the problem
- **Backward compatibility** — every header starts with a magic string and a layout version, so new library versions can always read old data
- **No `pre_upgrade` hooks** — structures must not require migration on upgrade
- **Limited blast radius** — a bug in one structure cannot corrupt another
- **No reallocation** — moving data in bulk is too expensive in cycles; all growth happens in place
- **Multi-memory compatibility** — the design works with multiple stable memories, ensuring forward compatibility with upcoming IC features

The six structures the library ships:

| Structure  | Description                       | Type support        | Memories needed  |
|------------|-----------------------------------|---------------------|------------------|
| `Cell`     | Single serializable value         | Bounded + Unbounded | 1                |
| `BTreeMap` | Ordered key-value store           | Bounded + Unbounded | 1                |
| `BTreeSet` | Ordered set of unique keys        | Bounded + Unbounded | 1                |
| `Vec`      | Growable array                    | Bounded only        | 1                |
| `Log`      | Append-only variable-size entries | Bounded + Unbounded | 2 (index + data) |
| `MinHeap`  | Priority queue                    | Bounded only        | 1                |

## Segment 2 — Core abstractions (15 min)

### 2a. The Memory trait (`src/lib.rs:52-93`)

Everything in the library is generic over a single four-method trait:

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

`RestrictedMemory` (`src/lib.rs:243-308`) is a public `Memory` adapter that exposes a fixed page range of a larger memory as its own address space starting at 0. It is the simpler alternative to `MemoryManager` for cases where each structure's maximum size is known upfront — covered in more detail in section 2c.

### 2b. The Storable trait (`src/storable.rs:13-72`)

Stable structures are generic and work only with raw bytes — they have no knowledge of the types stored in them. `Storable` is the bridge: it tells a structure how to convert a value to and from bytes. Any type you want to store must implement it. The library already provides implementations for the most common types; custom types require a manual implementation:

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

The library ships `Storable` implementations for all primitives (`u8` through `u128`, `f32`/`f64`, `bool`, `[u8; N]`), `String`, `Vec<u8>`, `Principal`, `Option<T>`, and tuples.

Note: `Storable` says nothing about the serialization format. Users commonly use CBOR (`ciborium`), protobuf, or Candid inside `to_bytes`/`from_bytes`. See `docs/src/schema-upgrades.md` for patterns for adding fields safely.

### 2c. The MemoryManager (`src/memory_manager.rs`)

Each stable structure requires exclusive ownership of its memory — sharing causes corruption. The naive alternative, carving stable memory into static regions via `RestrictedMemory`, has two problems: you must know the size limit upfront, and the full region is paid for even when mostly empty.

`MemoryManager` eliminates both problems. It presents each structure with a `VirtualMemory` that has no upfront size limit and grows on demand. Underneath, it divides the real stable memory into 128-page buckets allocated as needed and interleaved freely across virtual memories — so total stable memory usage stays proportional to actual data, not declared limits.

```
1) NAIVE (RestrictedMemory) — limits declared upfront, full region allocated immediately

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

### 2d. Internal allocators (contributor-level)

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


## Segment 3 — Lifecycle, schema upgrades, and migrations (10 min)

### 3a. Lifecycle across upgrades

Every stable structure has two constructors:

- `new(memory)` — writes a fresh magic header and initialises an empty structure
- `init(memory)` — checks for the magic header; loads the existing structure if found, creates a new one otherwise

Always use `init` in a canister. Because stable memory survives upgrades, calling `init` on next deployment finds the existing data and resumes from it — no `pre_upgrade`/`post_upgrade` needed. The magic header also carries a layout version, so new library versions can always read data written by older ones.

### 3b. Layout versioning in practice: BTreeMap V1 → V2

`BTreeMap` is currently the only structure that has shipped two layout versions, and its migration is a concrete example of the backward-compatibility principle above:

- **V1** supports only `Bound::Bounded` types. Page size is derived from `max_key_size` and `max_value_size` stored in the header.
- **V2** adds support for `Bound::Unbounded` types via explicit page sizes and overflow pages — nodes can chain multiple pages when a value exceeds the page size.

Migration from V1 to V2 is **transparent and non-breaking**: calling `BTreeMap::init()` on an existing V1 map automatically upgrades it to V2 on first load — existing data is preserved, no user action required. Under the hood, `init()` calls `load_helper(memory, migrate_to_v2: true)`, which re-interprets the stored `max_key_size`/`max_value_size` as a `DerivedPageSize` for the V2 allocator. Loading a V2 map as V1 is rejected at startup.

### 3c. Schema upgrades

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

### 3d. Data migrations

When an in-place field addition isn't enough — e.g. changing the key type or restructuring the value layout entirely — data must be migrated from one structure to another.

For anything beyond a trivial dataset, migration cannot happen in a single upgrade call. The IC enforces a per-round instruction limit, so even a moderately large structure will trap if you try to read-transform-write it all at once.

The practical approach is to run the migration incrementally across many canister update calls:

1. Create the new structure under a fresh `MemoryId` alongside the old one.
2. Each update call migrates a small batch of records from old to new, tracking progress in a version field or migration cursor.
3. During migration, both structures are live. A routing layer directs reads and writes to whichever structure owns each record — unmigrated records go to the old structure, already-migrated ones to the new.
4. Once all records are migrated, the routing layer is dropped and the old structure is cleared.

This is the pattern NNS-dapp used when migrating accounts to stable memory: two schemas active simultaneously, new writes applied to both during the transition, migration driven by a periodic job chunk by chunk.

The cost to be aware of: both structures occupy stable memory simultaneously (~2× peak usage), and after the old structure is cleared its buckets remain permanently assigned to its `MemoryId` — they cannot be reclaimed or reused. Budget for this when planning large schema changes.

### 3e. MemoryManager limitations and the path to bucket reclamation

The inability to reuse freed buckets is a known limitation rooted in a structural invariant of the current MemoryManager: **buckets within each virtual memory must be stored in ascending order by ID**. Because the header encodes only the owning `MemoryId` per bucket (1 byte), there is no room to store an explicit ordering — the order is implied by bucket position. To load a virtual memory correctly, the runtime simply scans for all buckets belonging to that `MemoryId` and traverses them in ID order.

This makes safe reuse impossible in the typical migration layout. When structure A occupies buckets 0–99 and is cleared, structure B (buckets 100–199) cannot absorb A's freed buckets — they have lower IDs than B's current maximum, so inserting them would violate the ascending invariant and corrupt B's data on the next load.

#### Attempted fix: conservative bucket reuse

A partial fix, **conservative bucket reuse**, was implemented and then [reverted](https://github.com/dfinity/stable-structures/pull/396). It allowed reuse only of freed buckets with IDs *higher* than the growing virtual memory's current maximum — a constraint that is almost never satisfied in practice, since A allocates first and therefore always has lower IDs than B.

#### Alternative design: explicit linked list of buckets

The proper solution requires a new header layout. The alternative design replaces implicit ID ordering with an **explicit linked list**: each bucket stores a 4-byte pointer to the next bucket in its virtual memory's chain. Freeing a virtual memory then simply nulls out its head pointer, making all its buckets immediately available for any new allocation regardless of their IDs.

The redesign also removes the current 32,768-bucket cap (`MAX_NUM_BUCKETS`), raising it to 2^32 and lifting the effective stable memory ceiling from 256 GiB to well beyond current IC capacity.

The tradeoff: this is a **breaking change**. The on-disk header format is incompatible with the current layout, so existing canisters will need a one-time migration when the new MemoryManager ships.

## Segment 4 — Code walkthrough: BTreeMap::insert (25 min)

`StableBTreeMap` is the most complex and most commonly used structure. Walking an insert from the public API down to raw byte writes shows every major mechanism.

### 4a. File layout

| File | Purpose |
|---|---|
| `src/btreemap.rs` | Public API, header format, `init`/`load`, `insert`/`get`/`remove` |
| `src/btreemap/allocator.rs` | Free-list chunk allocator for node pages |
| `src/btreemap/node.rs` | In-memory `Node` representation, load/save dispatch |
| `src/btreemap/node/v1.rs` | Node serialization for bounded types (legacy) |
| `src/btreemap/node/v2.rs` | Node serialization for bounded and unbounded types |
| `src/btreemap/iter.rs` | Range iteration |

### 4b. Memory layout on disk (`src/btreemap.rs:1-50`)

Address 0 in the memory given to `BTreeMap`:

```
"BTR" magic                    ↕ 3 bytes
layout version                 ↕ 1 byte      (1 = V1, 2 = V2)
max_key_size or page_size      ↕ 4 bytes
max_value_size or marker       ↕ 4 bytes
root node address              ↕ 8 bytes
length / element count         ↕ 8 bytes
reserved                       ↕ 24 bytes
Allocator header               ↕ starts at offset 52 (ALLOCATOR_OFFSET)
Node pages                     ...
```

### 4c. The Allocator (`src/btreemap/allocator.rs`)

The allocator is a free-list of same-size chunks. The chunk size is determined at `BTreeMap::new()` time:

- If both `K` and `V` are `Bounded`: `page_size = max_node_size * 3/4` (covers ~70% of real-world nodes at 8/11 capacity)
- Otherwise: `page_size = 1024` bytes (`DEFAULT_PAGE_SIZE`)

Each chunk on the free list contains a `ChunkHeader` (magic `"CHK"`, next-free pointer) followed by the usable data area. Allocation pops from the head; deallocation pushes back.

### 4d. BTreeMap::init (`src/btreemap.rs:274-290`)

```
if memory.size() == 0  →  BTreeMap::new (writes a fresh header)
else                   →  check for "BTR" magic and call BTreeMap::load
```

`BTreeMap::load` reads the header, detects the layout version (V1 or V2), and can transparently migrate V1 to V2 on first load.

### 4e. BTreeMap::insert — the critical path

Trace in `src/btreemap.rs` around line 500:

1. Call `insert(key, value)` on `BTreeMap<K, V, M>`
2. If `root_addr == NULL`: allocate a new leaf node via `allocator.allocate()`, save an empty `Node`, set `root_addr`
3. Otherwise: load the root `Node` from memory (`Node::load` reads the node header to detect V1/V2, then deserializes keys, values, and children addresses)
4. Walk down the tree: at each internal node, binary-search entries to find the child pointer, load that child
5. At the leaf: insert the `(key, value)` entry, keeping entries sorted by key
6. If the leaf now has `CAPACITY` (11) entries: split — allocate a new node, distribute entries, push the median key up to the parent
7. Splits propagate up; if the root splits, a new root node is allocated
8. Every modified node is saved: `Node::save` serializes back to raw bytes in the allocated chunk via `memory.write()`

### 4f. V2 node serialization (`src/btreemap/node/v2.rs`)

Initial page layout:

```
magic "BTN"             ↕ 3 bytes
layout version (2)      ↕ 1 byte
node type               ↕ 1 byte
entry count (k)         ↕ 2 bytes
overflow address        ↕ 8 bytes
child addresses         ↕ 8 bytes each, up to k + 1
key blobs               with 1/2/4-byte length prefix if not fixed-size
value blobs             with 1/2/4-byte length prefix if not fixed-size
```

If the serialized content exceeds the page size, overflow pages are chained. Each overflow page has a `"NOF"` magic, a next-overflow pointer, and continuation data.

### 4g. The Storable round-trip

```
save:  value.into_bytes_checked()  →  write length prefix if needed  →  write bytes
load:  read length prefix if needed  →  read bytes  →  V::from_bytes(bytes)
```

`insert` receives the value by value, so the library calls `into_bytes_checked()` rather than `to_bytes_checked()` — the value is consumed directly into a `Vec<u8>` with no intermediate clone for owned types.

This is where `BOUND` matters in practice. A fixed-size key writes 0 bytes of overhead per entry. An unbounded value always writes a length prefix and can use as many bytes as needed.

## Segment 5 — Local development loop (10 min)

### Building and testing

```sh
cargo build
cargo test                          # runs all unit and property tests
cargo test -p ic-stable-structures  # library tests only
```

The `btreemap` module has property-based tests in `src/btreemap/proptests.rs` using `proptest`. They generate random sequences of inserts, removes, and gets and compare the stable `BTreeMap` against `std::collections::BTreeMap`.

### Fuzzing (requires nightly)

```sh
rustup toolchain install nightly
cargo install cargo-fuzz
cargo +nightly fuzz list
cargo +nightly fuzz run stable_btreemap_multiple_ops_persistent
```

The fuzz targets in `fuzz/fuzz_targets/` run random multi-operation sequences and check for crashes and invariant violations. The `_persistent` variants reuse a single in-memory structure across iterations, which finds bugs from state accumulation.

### Benchmarks

Benchmarks use `canbench-rs` (`benchmarks/btreemap/src/main.rs`). They measure **instruction counts**, not wall time, because instructions are the actual cost unit on the IC.

```sh
cargo install canbench
cd benchmarks/btreemap && canbench
```

Key benchmark families:

- `btreemap_insert_blob_*` — inserts with different key/value sizes (4 to 1024 bytes)
- `btreemap_get_blob_*` — random lookups at scale
- `btreemap_iter_*` — full iteration cost

### Checklist for new contributions

1. Write unit tests inside the module (see `src/btreemap/node/tests.rs` as a model)
2. Add or extend a proptest suite to catch invariant violations
3. Add a benchmark if the change affects hot paths
4. If the on-disk format changes, bump the version constant and add a load path for the old version — **never break backward compatibility**

## Key files to bookmark

| File | What's there |
|---|---|
| `src/lib.rs` | `Memory` trait, `safe_write`, `RestrictedMemory` |
| `src/storable.rs` | `Storable` trait, `Bound` enum, primitive impls |
| `src/memory_manager.rs` | `MemoryManager`, `VirtualMemory`, bucket layout |
| `src/btreemap.rs` | `BTreeMap` header, `init`, `insert`, `get`, `remove` |
| `src/btreemap/allocator.rs` | Chunk allocator |
| `src/btreemap/node/v2.rs` | Node V2 on-disk format |
| `examples/src/basic_example/src/lib.rs` | Minimal canister template |
| `docs/src/schema-upgrades.md` | How to evolve types safely |
| `benchmarks/btreemap/src/main.rs` | Benchmark structure to copy |
