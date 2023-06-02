#![allow(dead_code)]
//! This module implements a certified sequence data structure
//! compatible with the [IC certification scheme](https://internetcomputer.org/docs/current/references/ic-interface-spec#certification).
//!
//! The implementation is based on Dat's Hypercore [Flat Trees](https://dat-ecosystem-archive.github.io/book/ch01-01-flat-tree.HTML)
//! but has important differences in how it handles independent forests.
//!
//! A certified sequence is a flat in-order tree stored as a stable array of hashes.
//! Items at even indices are hashes of the values; items at odd indices are internal nodes.
//! The number of elements in the tree is always odd and equal to (2 * n - 1) where n is leaves count.
//!
//! For example, we represent a tree with 7 leaves as an array with 13 nodes.
//!
//! ```text
//! H | 0 1 2 3 4 5 6 7 8 9 a b c
//!             ______x_____
//!            /            \
//!           x              \
//!          / \              x
//!         /   \           _/ \
//!       x       x       x     `
//!      / \     / \     / \    |
//! T | 0 _ 1 _ 3 _ 4 _ 5 _ 6 _ 7
//! ```

#[cfg(test)]
mod tests;

use crate::StableVec;
use crate::{GrowFailed, Memory};
use sha2::{Digest, Sha256};

pub type Hash = [u8; 32];

type Repr<M> = StableVec<Hash, M>;

pub struct CertifiedSeq<M: Memory>(Repr<M>);

impl<M: Memory> CertifiedSeq<M> {
    pub fn new(m: M) -> Result<Self, GrowFailed> {
        Repr::<M>::new(m).map(Self)
    }

    /// Appends a new entry to the sequence.
    /// Returns the logical index of the entry.
    pub fn append(&self, bytes: &[u8]) -> Result<u64, GrowFailed> {
        let n = self.0.len();
        if n == 0 {
            // The first element is a special case.
            let h = leaf_hash(0, bytes);
            self.0.push(&h)?;

            debug_assert!(self.0.len() % 2 == 1);

            return Ok(0);
        }
        let logical_index = num_leaves(n);
        let mut right_hash = leaf_hash(logical_index, bytes);

        // Push a temporary internal node.
        self.0.push(&[0; 32])?;
        if let Err(e) = self.0.push(&right_hash) {
            // Remove the temporary node if there is no room for the
            // data node.
            let _ = self.0.pop();
            return Err(e);
        }

        let mut i = n + 1;

        while let Some(p) = left_parent(i) {
            let lc = left_child(p).unwrap();
            let left_hash = self.0.get(lc).unwrap();
            right_hash = fork_hash(&left_hash, &right_hash);
            self.0.set(p, &right_hash);
            i = p;
        }

        debug_assert!(self.0.len() % 2 == 1);

        Ok(logical_index)
    }

    /// Returns the root hash of the data structure.
    pub fn root_hash(&self) -> Hash {
        match self.root_index() {
            Some(i) => self.0.get(i).expect("BUG: tree root is not in the storage"),
            None => empty_hash(),
        }
    }

    /// Returns the logical number of entries in the sequence.
    pub fn num_entries(&self) -> u64 {
        num_leaves(self.0.len())
    }

    /// Returns the index of the root node.
    fn root_index(&self) -> Option<u64> {
        tree_root(self.0.len())
    }
}

// Returns an integer corresponding to the last set bit of n.
fn lsb(n: u64) -> u64 {
    n - (n & (n - 1))
}

/// Returns the index of the left child for node `i`.
/// Returns None if `i` is a leaf.
fn left_child(i: u64) -> Option<u64> {
    if i % 2 == 0 {
        return None;
    }
    Some(i - lsb((i + 1) / 2))
}

#[test]
fn test_left_child() {
    assert_eq!(left_child(0), None);
    assert_eq!(left_child(1), Some(0));
    assert_eq!(left_child(2), None);
    assert_eq!(left_child(3), Some(1));
    assert_eq!(left_child(5), Some(4));
    assert_eq!(left_child(7), Some(3));
    assert_eq!(left_child(9), Some(8));
    assert_eq!(left_child(11), Some(9));
    assert_eq!(left_child(13), Some(12));
    assert_eq!(left_child(15), Some(7));
}

/// Returns the index of the parent for node `i` if the parent is on
/// the left.
fn left_parent(i: u64) -> Option<u64> {
    if i == 0 {
        return None;
    }
    if i % 2 == 0 {
        return Some(i - 1);
    }
    let lt_size = 2 * lsb((i + 1) / 2) - 1;
    if i == lt_size {
        return None;
    }
    Some(i - lt_size - 1)
}

#[test]
fn test_left_parent() {
    for n in [0, 1, 3, 7] {
        assert_eq!(
            left_parent(n),
            None,
            "Node {} does not have a left parent",
            n
        )
    }
    for (n, p) in [
        (2, 1),
        (4, 3),
        (5, 3),
        (6, 5),
        (8, 7),
        (9, 7),
        (10, 9),
        (11, 7),
        (12, 11),
        (13, 11),
    ] {
        assert_eq!(
            left_parent(n),
            Some(p),
            "Expected the parent of node {} to be {}",
            n,
            p
        );
    }
}

/// Returns the number of leaves in a flat tree of the given size.
fn num_leaves(s: u64) -> u64 {
    debug_assert!(s == 0 || s % 2 == 1);
    // In a flat tree, we must have `s = 2n - 1`, where `n` is the leaf count.
    // Then `n = (s + 1) / 2`, which also gives the right answer if `s = 0`.
    (s + 1) / 2
}

/// Returns the index of the root node in the tree of the specified
/// size. Returns `None` if the tree is empty.
///
/// Precondition: `s = 0 \/ s % 2 = 1`
/// Postcondition: `s > 0 => tree_root(s) = Some(i): i < s`
fn tree_root(s: u64) -> Option<u64> {
    debug_assert!(s == 0 || s % 2 == 1);
    // The root is always after the first largest full subtree of size
    // less than or equal to s.  In other words, if `s = 2^k + q`,
    // where `q < 2^k`, then the result is `2^k - 1`.
    match s {
        0 => None,
        1 => Some(0),
        n => Some((1 << n.ilog2()) - 1),
    }
}

#[test]
fn test_tree_root() {
    assert_eq!(tree_root(0), None);
    assert_eq!(tree_root(1), Some(0));
    assert_eq!(tree_root(3), Some(1));
    assert_eq!(tree_root(5), Some(3));
    assert_eq!(tree_root(7), Some(3));
    assert_eq!(tree_root(9), Some(7));
    assert_eq!(tree_root(11), Some(7));
    assert_eq!(tree_root(13), Some(7));
}

/// Returns the hash of an empty tree.
fn empty_hash() -> Hash {
    domain_sep("ic-hashtree-empty").finalize().into()
}

fn fork_hash(lh: &Hash, rh: &Hash) -> Hash {
    let mut fork_hasher = domain_sep("ic-hashtree-fork");
    fork_hasher.update(lh);
    fork_hasher.update(rh);
    fork_hasher.finalize().into()
}

/// Returns the hash of a leaf labeled with the given index.
fn leaf_hash(idx: u64, bytes: &[u8]) -> Hash {
    let mut data_hasher = domain_sep("ic-hashtree-leaf");
    data_hasher.update(bytes);
    let data_hash: Hash = data_hasher.finalize().into();

    let mut labeled_hasher = domain_sep("ic-hashtree-labeled");
    labeled_hasher.update(&idx.to_be_bytes());
    labeled_hasher.update(&data_hash);
    labeled_hasher.finalize().into()
}

fn domain_sep(s: &str) -> sha2::Sha256 {
    let buf: [u8; 1] = [s.len() as u8];
    let mut h = Sha256::new();
    h.update(&buf[..]);
    h.update(s.as_bytes());
    h
}
