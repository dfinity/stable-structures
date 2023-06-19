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

use crate::base_vec::{BaseVec, InitError};
use crate::certification::WitnessBuilder;
use crate::{GrowFailed, Memory};
use sha2::{Digest, Sha256};

const MAGIC: [u8; 3] = *b"SCS"; // Short for "stable certified sequence"

pub type Hash = [u8; 32];

type Repr<M> = BaseVec<Hash, M>;

pub struct CertifiedSeq<M: Memory>(Repr<M>);

impl<M: Memory> CertifiedSeq<M> {
    pub fn new(memory: M) -> Result<Self, GrowFailed> {
        Repr::<M>::new(memory, MAGIC).map(Self)
    }

    pub fn init(memory: M) -> Result<Self, InitError> {
        Repr::<M>::init(memory, MAGIC).map(Self)
    }

    /// Appends a new entry to the sequence.
    /// Returns the logical index of the entry.
    pub fn append(&self, bytes: &[u8]) -> Result<u64, GrowFailed> {
        let n = self.0.len();
        let data_hash = leaf_hash(bytes);
        let logical_index = if n == 0 {
            // The first element is a special case.
            self.0.push(&data_hash)?;
            0
        } else {
            // Push a temporary internal node.
            self.0.push(&[0; 32])?;
            if let Err(e) = self.0.push(&data_hash) {
                // Remove the temporary node if there is no room for the
                // data node.
                let _ = self.0.pop();
                return Err(e);
            }

            let logical_index = num_leaves(n);
            let mut right_hash = leaf_subtree_hash(logical_index, &data_hash);

            let mut i = n + 1;
            while let Some(p) = left_parent(i) {
                let lc = left_child(p).unwrap();
                let left_hash = self.0.get(lc).unwrap();
                right_hash = if lc % 2 == 0 {
                    fork_hash(&leaf_subtree_hash(lc / 2, &left_hash), &right_hash)
                } else {
                    fork_hash(&left_hash, &right_hash)
                };
                self.0.set(p, &right_hash);
                i = p;
            }

            logical_index
        };

        debug_assert!(self.0.len() % 2 == 1);

        Ok(logical_index)
    }

    pub fn witness_item<B: WitnessBuilder>(&self, logical_index: u64, leaf_data: &[u8]) -> B::Tree {
        let n = self.0.len();

        let (mut pos, data_witness) = if logical_index < num_leaves(n) {
            debug_assert_eq!(self.0.get(logical_index * 2).unwrap(), leaf_hash(leaf_data));
            (logical_index * 2, B::leaf(leaf_data))
        } else {
            // Absence proof
            (n - 1, B::pruned(self.0.get(n - 1).unwrap()))
        };

        // Build witness bottom-up, starting with the leaf.
        let mut witness = B::node(&(pos / 2).to_be_bytes(), data_witness);
        loop {
            // LOOP INVARIANT: witness is a valid proof for a subtree rooted at pos.
            match node_parent(pos, n) {
                NodeParent::Root => break,
                NodeParent::LeftChildOf(p) => {
                    let right_hash = self.hash(right_child(p, n).unwrap());
                    witness = B::fork(witness, B::pruned(right_hash));
                    pos = p;
                }
                NodeParent::RightChildOf(p) => {
                    let left_hash = self.hash(left_child(p).unwrap());
                    witness = B::fork(B::pruned(left_hash), witness);
                    pos = p;
                }
            }
        }
        witness
    }

    fn hash(&self, i: u64) -> Hash {
        let hash = self
            .0
            .get(i)
            .expect("BUG: requested a node that is not in the storage");
        if i % 2 == 0 {
            leaf_subtree_hash(i / 2, &hash)
        } else {
            hash
        }
    }

    /// Returns the root hash of the sequence.
    pub fn root_hash(&self) -> Hash {
        match self.root_index() {
            Some(i) => self.hash(i),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NodeParent {
    Root,
    LeftChildOf(u64),
    RightChildOf(u64),
}

fn node_parent(i: u64, n: u64) -> NodeParent {
    if Some(i) == tree_root(n) {
        return NodeParent::Root;
    }
    let p = full_tree_parent(i);
    if n <= p {
        // The full tree parent is outside of the tree.
        // The node must be attached to the left parent.
        return NodeParent::RightChildOf(left_parent(i).unwrap());
    }
    if is_full_tree_left_child(i) {
        NodeParent::LeftChildOf(p)
    } else {
        NodeParent::RightChildOf(p)
    }
}

#[test]
fn test_node_parent() {
    use NodeParent::*;
    let answers = [
        LeftChildOf(1),
        LeftChildOf(3),
        RightChildOf(1),
        LeftChildOf(7),
        LeftChildOf(5),
        RightChildOf(3),
        RightChildOf(5),
        Root,
        LeftChildOf(9),
        LeftChildOf(11),
        RightChildOf(9),
        RightChildOf(7),
        RightChildOf(11),
    ];
    for (node, answer) in answers.into_iter().enumerate() {
        assert_eq!(
            node_parent(node as u64, answers.len() as u64),
            answer,
            "Failed for node {node}"
        );
    }
}

/// Returns an integer corresponding to the last set bit of n.
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

fn full_tree_right_child(i: u64) -> Option<u64> {
    if i % 2 == 0 {
        return None;
    }
    let b = lsb(i + 1);
    Some(i + b - (b >> 1))
}

#[test]
fn test_full_tree_right_child() {
    let answers = [
        None,
        Some(2),
        None,
        Some(5),
        None,
        Some(6),
        None,
        Some(11),
        None,
        Some(10),
        None,
        Some(13),
        None,
        Some(14),
        None,
    ];
    for (node, answer) in answers.into_iter().enumerate() {
        assert_eq!(
            full_tree_right_child(node as u64),
            answer,
            "Failed on node {node}"
        );
    }
}

fn right_child(i: u64, n: u64) -> Option<u64> {
    let candidate = full_tree_right_child(i)?;
    if candidate < n {
        Some(candidate)
    } else {
        Some(i + 1 + tree_root(n - i - 1)?)
    }
}

#[test]
fn test_right_child() {
    assert_eq!(right_child(15, 19), Some(17));
    assert_eq!(right_child(11, 13), Some(12));
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

/// Returns the parent of node i within a full binary tree.
fn full_tree_parent(i: u64) -> u64 {
    let b = lsb(i + 1);
    (i + b) & !(b << 1)
}

#[test]
fn test_full_tree_parent() {
    let parents = [1, 3, 1, 7, 5, 3, 5, 15, 9, 11, 9, 7, 13, 11, 13];
    for (i, p) in parents.iter().enumerate() {
        assert_eq!(
            full_tree_parent(i as u64),
            *p as u64,
            "Expected the parent of {i} to be {p}"
        );
    }
}

fn is_full_tree_left_child(i: u64) -> bool {
    i & (lsb(i + 1) << 1) == 0
}

#[test]
fn test_full_tree_is_left_child() {
    let table = [1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0];
    for (i, flag) in table.into_iter().enumerate() {
        assert_eq!(
            is_full_tree_left_child(i as u64),
            flag == 1,
            "Error for node {i}"
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

/// Returns the hash of a fork with the given subtrees.
fn fork_hash(lh: &Hash, rh: &Hash) -> Hash {
    let mut fork_hasher = domain_sep("ic-hashtree-fork");
    fork_hasher.update(lh);
    fork_hasher.update(rh);
    fork_hasher.finalize().into()
}

/// Returns the hash of a leaf containing the given bytes.
fn leaf_hash(bytes: &[u8]) -> Hash {
    let mut data_hasher = domain_sep("ic-hashtree-leaf");
    data_hasher.update(bytes);
    data_hasher.finalize().into()
}

/// Returns the hash of a leaf labeled with the given index.
fn leaf_subtree_hash(idx: u64, data_hash: &Hash) -> Hash {
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
