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

After changing code, always run at least `cargo fmt --all -- --check` and `cargo clippy --tests --benches -- -D clippy::all`. 
Run `cargo test` when changes affect logic.

## Code style

- Follow existing patterns in the codebase
- No unnecessary comments, docstrings, or type annotations on unchanged code
- Test names should describe the invariant being checked

## Commit messages

- Use conventional commit prefix (test, feat, fix, perf, refactor, docs, chore, ci)
- First line: under 70 characters, short summary of what changed
- Body (if needed): why the change was made, not how
- Must be correct, short, clear and informative

## PR title and description

When asked to "write PR description" or similar:
- Look at all commits in the current branch vs main
- Title: under 70 characters, use conventional commit prefix (test, feat, fix, perf, refactor, docs, chore, ci)
- Description: a single line summary on top, followed by a short explanation of what was added and why
- Both must be correct, short, clear and informative
- Do not use excessive formatting, but use bullet points or tables if it improves readability
- Don't list commits or files changed, the PR view already shows that
