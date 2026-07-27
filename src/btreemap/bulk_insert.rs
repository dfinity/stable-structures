//! Batched insertion for [`BTreeMap`].
//!
//! [`BTreeMap::insert_many`] inserts a stream of pairs while holding the current
//! root-to-leaf path in memory, so that each modified node is written to stable memory
//! once the input moves past it rather than once per key. [`BulkInsert`] is that held
//! path, and [`PathLevel`] is one level of it.
//!
//! # Attributing the cost
//!
//! Building with the `bench_scope` feature splits a batch into four canbench scopes:
//!
//! - `bulk_insert_release` — a node leaving the path: written out if dirty, else returned
//!   to the node cache
//! - `bulk_insert_descend` — taking one child out of the cache and recording its bounds
//! - `bulk_insert_leaf` — placing the entry, *including* any split it triggers
//! - `bulk_insert_split` — the split cascade, nested inside the previous one
//!
//! So the cost of placing an entry with no split is `bulk_insert_leaf` minus
//! `bulk_insert_split`. The feature is off by default and adds significant overhead, so
//! the numbers are for comparing parts against each other within one run, not against
//! results measured without it.

use crate::btreemap::node::{Node, NodeType};
use crate::types::NULL;
use crate::{BTreeMap, Memory, Storable};

/// One level of the root-to-leaf path that [`BTreeMap::insert_many`] holds open across a
/// run of inserts.
struct PathLevel<K: Storable + Ord + Clone> {
    node: Node<K>,

    /// Index of this node among its parent's children. Meaningless for the root.
    index_in_parent: usize,

    /// The key range this node is responsible for, taken from the separators either side of
    /// it while descending. Both ends are exclusive, because a separator key is stored in
    /// the parent rather than the child. `None` means unbounded on that side, which is
    /// always the case for the root.
    ///
    /// Both ends are tracked, not just the upper one, so that a key arriving out of order
    /// is detected rather than being dropped into the wrong node. See [`PathLevel::covers`].
    lower: Option<K>,
    upper: Option<K>,

    /// Distance from the root, needed when handing the node back to the node cache.
    depth: u8,

    /// Whether the node has been modified and so must be written out, rather than simply
    /// returned to the cache, when it leaves the path.
    dirty: bool,
}

impl<K: Storable + Ord + Clone> PathLevel<K> {
    /// Whether `key` belongs somewhere under this node.
    ///
    /// For an ascending batch only the upper bound can ever fail, and that is the case this
    /// is tuned for. The lower bound is checked too so that an out-of-order key unwinds
    /// past this node — as far as the root if need be — instead of being inserted here,
    /// which would break the ordering invariant of the tree.
    fn covers(&self, key: &K) -> bool {
        self.lower.as_ref().is_none_or(|lower| lower < key)
            && self.upper.as_ref().is_none_or(|upper| key < upper)
    }
}

/// Inserts a stream of keys while keeping the current root-to-leaf path in
/// memory, so that each modified node is written to stable memory once the batch moves
/// past it rather than once per key.
///
/// Dropping a `BulkInsert` writes back whatever it is still holding: the remaining path,
/// and the header if `length` or `root_addr` moved. That is how a batch is completed, so
/// the drop is load-bearing on every call.
pub(super) struct BulkInsert<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    map: &'a mut BTreeMap<K, V, M>,

    /// Root first, leaf last. Empty only before the first insert.
    path: Vec<PathLevel<K>>,

    /// Whether `length` or `root_addr` changed and the header still needs writing.
    header_dirty: bool,
}

impl<'a, K, V, M> BulkInsert<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    pub(super) fn new(map: &'a mut BTreeMap<K, V, M>) -> Self {
        Self {
            map,
            path: Vec::new(),
            header_dirty: false,
        }
    }

    /// Releases a node that has left the path: written out if modified, handed back to the
    /// node cache otherwise.
    fn release(&mut self, level: PathLevel<K>) {
        #[cfg(feature = "bench_scope")]
        let _p = canbench_rs::bench_scope("bulk_insert_release"); // May add significant overhead.

        let mut node = level.node;
        if level.dirty {
            self.map.save_node(&mut node);
        } else {
            self.map.return_node(node, level.depth);
        }
    }

    /// Releases the whole path, leaving it empty.
    fn release_path(&mut self) {
        while let Some(level) = self.path.pop() {
            self.release(level);
        }
    }

    pub(super) fn insert(&mut self, key: K, value: V) {
        // Drop back up the path until we reach a node that still covers this key. Since the
        // batch ascends, a node stops covering once the keys pass its upper bound.
        while self.path.last().is_some_and(|level| !level.covers(&key)) {
            let level = self.path.pop().expect("just checked that one exists");
            self.release(level);
        }

        if self.path.is_empty() {
            self.push_root();
        }

        // Walk down to a leaf, taking each child out of the node cache as we go.
        loop {
            let bottom = self.path.last().expect("the path always holds a root here");
            if bottom.node.node_type() == NodeType::Leaf {
                break;
            }
            match bottom.node.search(&key, self.map.memory()) {
                Ok(idx) => {
                    // The key lives in this internal node; overwrite it where it sits.
                    let bottom = self.path.last_mut().expect("checked above");
                    bottom.node.set_value(idx, value.into_bytes_checked());
                    bottom.dirty = true;
                    return;
                }
                Err(idx) => self.push_child(idx),
            }
        }

        self.insert_into_leaf(key, value);
    }

    /// Starts a fresh path at the root, allocating one if the map is empty.
    fn push_root(&mut self) {
        let node = if self.map.root_addr == NULL {
            let node = self.map.allocate_node(NodeType::Leaf);
            self.map.root_addr = node.address();
            self.header_dirty = true;
            node
        } else {
            self.map.take_or_load_node(self.map.root_addr)
        };
        self.path.push(PathLevel {
            node,
            index_in_parent: 0,
            lower: None,
            upper: None,
            depth: 0,
            dirty: false,
        });
    }

    /// Descends one level, into the child at `idx` of the node currently at the bottom.
    fn push_child(&mut self, idx: usize) {
        #[cfg(feature = "bench_scope")]
        let _p = canbench_rs::bench_scope("bulk_insert_descend"); // May add significant overhead.

        let (address, lower, upper, depth) = {
            let bottom = self.path.last().expect("only called while descending");
            // The separators either side of this child bound the keys it may hold; beyond
            // the outermost separator the child inherits its parent's bound.
            let lower = if idx > 0 {
                Some(bottom.node.key(idx - 1, self.map.memory()).clone())
            } else {
                bottom.lower.clone()
            };
            let upper = if idx < bottom.node.entries_len() {
                Some(bottom.node.key(idx, self.map.memory()).clone())
            } else {
                bottom.upper.clone()
            };
            (
                bottom.node.child(idx),
                lower,
                upper,
                bottom.depth.saturating_add(1),
            )
        };
        let node = self.map.take_or_load_node(address);
        self.path.push(PathLevel {
            node,
            index_in_parent: idx,
            lower,
            upper,
            depth,
            dirty: false,
        });
    }

    /// Places `key` in the leaf at the bottom of the path, splitting it first if it is
    /// full.
    fn insert_into_leaf(&mut self, key: K, value: V) {
        // Encloses `bulk_insert_split`, so subtract that to get the cost of placing the
        // entry alone.
        #[cfg(feature = "bench_scope")]
        let _p = canbench_rs::bench_scope("bulk_insert_leaf"); // May add significant overhead.

        let search = {
            let leaf = self.path.last().expect("bottom is a leaf here");
            leaf.node.search(&key, self.map.memory())
        };

        let idx = match search {
            Ok(idx) => {
                let leaf = self.path.last_mut().expect("checked above");
                leaf.node.set_value(idx, value.into_bytes_checked());
                leaf.dirty = true;
                return;
            }
            Err(idx) => idx,
        };

        let idx = if self
            .path
            .last()
            .expect("bottom is a leaf here")
            .node
            .is_full()
        {
            self.split_leaf(&key);
            // The split moved half the entries out and may have swapped in the other half
            // entirely, so the position found above no longer means anything. Both halves
            // are at the minimum size, so there is room for the key wherever it now lands.
            self.path
                .last()
                .expect("bottom is a leaf here")
                .node
                .search(&key, self.map.memory())
                .expect_err("the key was absent and a split cannot introduce it")
        } else {
            // Nothing has touched the leaf since the search above, so reuse its answer.
            idx
        };

        let leaf = self.path.last_mut().expect("bottom is a leaf here");
        leaf.node
            .insert_entry(idx, (key, value.into_bytes_checked()));
        leaf.dirty = true;
        self.map.length += 1;
        self.header_dirty = true;
    }

    /// Makes room for `key` in the full leaf at the bottom of the path.
    ///
    /// A leaf split promotes a median into the parent, which may itself be full, so the
    /// split cascades up the path through every full ancestor — growing a new root if the
    /// whole path is full. Afterwards the bottom of the path is the half that owns `key`,
    /// with room for it.
    fn split_leaf(&mut self, key: &K) {
        #[cfg(feature = "bench_scope")]
        let _p = canbench_rs::bench_scope("bulk_insert_split"); // May add significant overhead.

        // Find the topmost level that has to split. Everything from there down to the leaf
        // is full, so none of them has anywhere to promote a median until the level above
        // it has split and made room.
        let mut topmost = self.path.len() - 1;
        while topmost > 0 && self.path[topmost - 1].node.is_full() {
            topmost -= 1;
        }

        if topmost == 0 {
            // The root is full too, so the tree gains a level and everything already on the
            // path moves one deeper.
            self.grow_root();
            topmost = 1;
        }

        // Split downwards. Each split leaves its node half empty, so by the time the level
        // below it splits, there is room for the median it promotes.
        for level in topmost..self.path.len() {
            self.split_level(level, key);
        }
    }

    /// Inserts a fresh internal root above the current one, leaving the tree a level deeper
    /// and the path a level longer. The new root holds the old one as its only child, and
    /// so has room for the median about to be promoted into it.
    fn grow_root(&mut self) {
        let old_root = self.path[0].node.address();
        let mut root = self.map.allocate_node(NodeType::Internal);
        root.push_child(old_root);
        self.map.root_addr = root.address();
        self.header_dirty = true;

        for level in self.path.iter_mut() {
            level.depth = level.depth.saturating_add(1);
        }
        self.path.insert(
            0,
            PathLevel {
                node: root,
                index_in_parent: 0,
                lower: None,
                upper: None,
                depth: 0,
                dirty: true,
            },
        );
    }

    /// Splits the full node at `path[index]` in two and promotes the median into its
    /// parent, which must have room. The path keeps whichever half owns `key`; the other
    /// half is finished with and is written out.
    fn split_level(&mut self, index: usize, key: &K) {
        debug_assert!(index > 0, "the root splits only after `grow_root`");
        debug_assert!(!self.path[index - 1].node.is_full());
        debug_assert!(self.path[index].node.is_full());

        let mut right = self.map.allocate_node(self.path[index].node.node_type());
        let right_addr = right.address();
        let (median_key, median_value) = self.path[index].node.split(&mut right, self.map.memory());
        let index_in_parent = self.path[index].index_in_parent;

        let parent = &mut self.path[index - 1];
        parent.node.insert_child(index_in_parent + 1, right_addr);
        parent
            .node
            .insert_entry(index_in_parent, (median_key.clone(), median_value));
        parent.dirty = true;

        // Keep whichever half the key belongs to; the other one is finished with. The key
        // cannot equal the median, which was already in the tree while the key was not.
        // The median becomes the boundary between the two halves.
        //
        // The levels below keep the bounds they already have: the separators either side of
        // them survive the split, they just end up in one half or the other.
        if *key < median_key {
            // The left half stays where it is, since `split` left it in place.
            let level = &mut self.path[index];
            level.upper = Some(median_key);
            level.dirty = true;
            self.map.save_node(&mut right);
        } else {
            let (mut left, children_kept_left) = {
                let level = &mut self.path[index];
                let left = core::mem::replace(&mut level.node, right);
                level.index_in_parent = index_in_parent + 1;
                level.lower = Some(median_key);
                level.dirty = true;
                let children_kept_left = left.children_len();
                (left, children_kept_left)
            };
            self.map.save_node(&mut left);

            // The level below travelled with the entries into the right half, so it sits at
            // a lower index among its parent's children than it did before.
            if let Some(below) = self.path.get_mut(index + 1) {
                // It has to have been in the right half: it covers `key`, and `key` is
                // above the median, so its index was at least the number of children the
                // left half kept.
                debug_assert!(below.index_in_parent >= children_kept_left);
                below.index_in_parent -= children_kept_left;
            }
        }
    }
}

impl<K, V, M> Drop for BulkInsert<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    fn drop(&mut self) {
        self.release_path();
        if self.header_dirty {
            self.map.save_header();
        }
    }
}
