# Design Principles

The library is built on several key principles:

* **Radical simplicity**: Each data structure follows the most straightforward design that solves the problem at hand.
This makes the code easier to understand, debug, and maintain.

* **Backward compatibility**: Upgrading the library version must preserve the data.
All data structures have a metadata section with the layout version, ensuring that new versions can read data written by old versions.

* **No [`pre_upgrade` hooks](https://internetcomputer.org/docs/references/ic-interface-spec#system-api-upgrades)**: A bug in the `pre_upgrade` hook can make your canister non-upgradable.
The best way to avoid this issue is not to have a `pre_upgrade` hook at all.

* **Limited blast radius**: If a single data structure has a bug, it should not corrupt the contents of other data structures.
This isolation helps prevent cascading failures.

* **No reallocation**: Moving large amounts of data is expensive and can lead to prohibitively high cycle consumption.
All data structures must manage their memory without costly moves.

* **Compatibility with multi-memory WebAssembly**: The design should work when canisters have multiple stable memories.
This ensures future compatibility with upcoming IC features. 
