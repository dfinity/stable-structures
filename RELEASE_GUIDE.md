# Release Guide (stable-structures)

This guide describes how to cut releases and publish them to [crates.io](https://crates.io) for `ic-stable-structures`.

## Goals

- Ship improvements without breaking users  
- Validate APIs and memory model before stabilization  
- Keep rollback cheap  

## Release Options

- **Opt-in feature flags**  
  Hide experimental code behind non-default flags.

- **Semantic Versioning Pre-Releases** ([semver.org](https://semver.org))  
  - `x.y.z-alpha.N` — experimental, incomplete, may be unstable or buggy  
  - `x.y.z-beta.N` — feature complete, testing needed, bugs expected  
  - `x.y.z-rc.N` — release candidate, no new features, only bug fixes  

Cargo won’t auto-pick pre-releases; users must pin them explicitly.

## Policy

- Any breaking and/or major change requires a **design doc** reviewed by stakeholders before release.  
- Pre-releases (`-alpha`, `-beta`, `-rc`) are strongly encouraged for high-risk changes.  

## When to Use (stable-structures specific)

- **Public API changes**  
  - Added methods → behind a feature flag until validated  
  - Removed/signature changes → breaking (minor bump <1.0.0, major bump ≥1.0.0)

- **Stable memory layout changes**  
  - New/altered layout → feature flag + pre-release  
  - Layout-breaking (cannot read old data) → breaking (minor bump <1.0.0, major bump ≥1.0.0)

- **Processing-only changes** (no layout change)  
  - Compatible algorithmic updates → minor bump  
  - High risk → feature flag and/or pre-release

- **Hidden layout migrations** (auto-migrate on load)  
  - If old data won’t load without migration → treat as breaking  
  - Ship via feature flag + pre-releases; promote only after successful trials  

## Example: Memory Reclaim

Adding a `reclaim()` method to free unused memory without changing layout, only processing it differently, is high risk and may cause data corruption:

- Hide `reclaim()` behind a feature flag  
- High risk → release as `-beta.N`  
- Iterate with feedback, promote to stable once validated  
- Remove feature flag after stabilization  

## Release Process

### Prepare

1. Bump version in `Cargo.toml`:

   ```toml
   [package]
   version = "x.y.z"
   ```

2. Ensure CI is green.  
3. Preferable commit & PR name: `chore(release): vX.Y.Z` ([example PR](https://github.com/dfinity/stable-structures/pull/379)).  

### Publish Release to GitHub

1. Identify the commit to release.  
2. Draft a new release:  
   - Go to the [Releases](https://github.com/dfinity/stable-structures/releases) tab.  
   - Click **Draft a new release**.  
   - Create a new tag `vX.Y.Z` pointing to the commit.  
   - Set the release title to `vX.Y.Z`.  
   - Choose the previous tag as the last release.  
   - Add release notes (GitHub can auto-generate, adjust as needed).  
3. Click **Publish release**.  

### Publish to crates.io

1. Generate an API token:  
   - Log in to crates.io → **Account Settings** → **API Tokens** → generate a new token.  
2. Authenticate:  
   ```bash
   cargo login
   ```
   Enter the token when prompted.  
3. Check out the repo at the release tag:  
   ```bash
   git checkout vX.Y.Z
   ```
4. Dry-run publish (mandatory):  
   ```bash
   cargo publish -p ic-stable-structures --dry-run
   ```
5. Publish:  
   ```bash
   cargo publish -p ic-stable-structures
   ```

### Verify

- Check [crates.io](https://crates.io/crates/ic-stable-structures).  
- Confirm documentation builds on [docs.rs](https://docs.rs).  
