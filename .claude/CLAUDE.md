# Project: ic-stable-structures

Rust library for data structures in Internet Computer stable memory.

## Local CI checks

Run these before pushing. They mirror the CI pipeline in `.github/workflows/ci.yml`.

```bash
# Format (must pass, instant)
cargo fmt --all -- --check

# Clippy (must pass, ~10s)
cargo clippy --tests --benches -- -D clippy::all

# Tests (must pass, ~80s)
cargo test
```

After changing code, always run at least `cargo fmt` and `cargo clippy --tests --benches -- -D clippy::all`. 
Run `cargo test` when changes affect logic.

## Code style

- Follow existing patterns in the codebase
- No unnecessary comments, docstrings, or type annotations on unchanged code
- Test names should describe the invariant being checked
