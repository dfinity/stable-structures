# AGENTS.md

## Overview

This repository provides stable data structures for the Internet Computer that persist across canister upgrades. These structures do not require `pre_upgrade` or `post_upgrade` hooks. The main modules include `BTreeMap` and `BTreeSet` for key-value storage and sets, `Vec` for growable arrays, `Cell` for single values, `Log` for append-only data, `MinHeap` for priority queues, and a `MemoryManager` for coordinating multiple structures in stable memory.
This repository provides stable data structures for the Internet Computer that persist across canister upgrades. These structures do not require `pre_upgrade` or `post_upgrade` hooks.

The main modules include:

- `BTreeMap` — key-value storage
- `BTreeSet` — sets
- `Vec` — growable arrays
- `Cell` — single values
- `Log` — append-only data
- `MinHeap` — priority queues
- `MemoryManager` — coordinates multiple structures in stable memory
## Index

Key entry points for understanding and using this library:

- `README.md` — quick start and basic usage patterns
- `docs/` — mdBook with concepts, design principles, and tutorials
- `src/lib.rs` — crate-level documentation and public API overview
- `examples/` — production-ready examples showing real-world usage
- `src/btreemap.rs`, `src/btreeset.rs`, `src/vec.rs`, etc. — individual module documentation
- `Cargo.toml` — version and dependency information

## Source of truth

Code defines behavior. Documentation must accurately reflect the current implementation. When making changes:

- update documentation in the same PR as code changes
- ensure examples compile and run correctly
- keep API documentation synchronized with function signatures
- update book chapters when changing core concepts

## Reading path

Follow this sequence to understand the library:

1. `README.md` for overview and quick examples
2. `docs/src/introduction/` for concepts and design principles
3. `docs/src/concepts/` for `Memory` trait and `MemoryManager` details
4. module documentation (`src/*.rs`) for specific data structure APIs
5. `examples/` for production usage patterns
6. code comments for implementation details

## Checklist

When changing public APIs:

- describe scope of changes in PR description
- update module-level documentation for affected types
- add or update runnable examples demonstrating the change
- update book chapters if concepts change
- verify `cargo doc` builds without warnings
- verify `mdbook build` succeeds
- test examples compile and run

## Quality bar

Every public type and module must have:

- short overview explaining purpose and use cases
- basic usage example that compiles
- links to related documentation or examples
- clear parameter and return value descriptions
- complexity information where relevant
- error conditions and panics documented
