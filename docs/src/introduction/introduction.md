# Introduction

## Background

Smart contracts on the [Internet Computer](https://internetcomputer.org) are referred to as [canisters](https://learn.internetcomputer.org/hc/en-us/articles/34210839162004-Canister-Smart-Contracts).

Canisters, compared to traditional smart contracts, have some unique properties including:

**Mutability**: A canister can have a set of controllers, and controllers are able to upgrade the code of the canister (e.g., to add new features, fix bugs, etc.)

**Scale**: Canisters have access to hundreds of gigabytes of memory and ample amounts of compute, allowing developers to build fully functioning dapps without relying on external cloud providers.

### The Challenge of Upgrades

When upgrading a canister, the canister's code is replaced with the new code.
In Rust, the new version of the code is not guaranteed to understand the memory layout established by the previous version.
This is because Rust's memory layout can change between different versions of the code, making it unsafe to directly access the old memory layout.
Therefore, by default, when a canister is upgraded and a new module is installed, the canister's main memory is wiped.

To persist state, the Internet Computer provides canisters with an additional memory called _stable memory_.
The conventional approach to canister state persistence follows these steps:

1. Serialize and store the state of the canister just before the upgrade using the `pre_upgrade` hook.
2. Install the new Wasm module of the canister (and wipe out the canister's main memory).
3. Deserialize the data that was stored in stable memory in step 1 using the `post_upgrade` hook.

This approach is easy to implement and works well for relatively small datasets.
Unfortunately, it does not scale well and can render a canister non-upgradable.

### The Solution: Stable Structures

Rather than using standard Rust data structures, which store their data in the canister's main memory, you can use stable structures.
Stable structures are designed to use stable memory as the primary storage, allowing them to grow to gigabytes in size without the need for `pre_upgrade`/`post_upgrade` hooks.
This is the key characteristic that distinguishes stable structures from Rust's standard data structures.
