use super::{
    node::{Node, NodeType},
    BTreeMap,
};
use crate::{types::NULL, Address, Memory, Storable};
use std::borrow::Cow;
use std::ops::{Bound, RangeBounds};

/// An indicator of the current position in the map.
pub(crate) enum Cursor<K: Storable + Ord + Clone> {
    Address(Address),
    Node { node: Node<K>, next: Index },
}

/// An index into a node's child or entry.
pub(crate) enum Index {
    Child(usize),
    Entry(usize),
}

/// An iterator over the entries of a [`BTreeMap`].
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    // A reference to the map being iterated on.
    map: &'a BTreeMap<K, V, M>,

    // A flag indicating if the cursors have been initialized yet.
    cursors_initialized: bool,

    // A stack of cursors indicating the current position in the tree.
    cursors: Vec<Cursor<K>>,

    // The range of keys we want to traverse.
    range: (Bound<K>, Bound<K>),
}

impl<'a, K, V, M> Iter<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    pub(crate) fn new(map: &'a BTreeMap<K, V, M>) -> Self {
        Self {
            map,
            cursors_initialized: false,
            cursors: vec![],
            range: (Bound::Unbounded, Bound::Unbounded),
        }
    }

    /// Returns an empty iterator.
    pub(crate) fn null(map: &'a BTreeMap<K, V, M>) -> Self {
        Self {
            map,
            cursors_initialized: true,
            cursors: vec![],
            range: (Bound::Unbounded, Bound::Unbounded),
        }
    }

    pub(crate) fn new_in_range(map: &'a BTreeMap<K, V, M>, range: (Bound<K>, Bound<K>)) -> Self {
        Self {
            map,
            cursors_initialized: false,
            cursors: vec![],
            range,
        }
    }

    pub(crate) fn new_with_cursors(
        map: &'a BTreeMap<K, V, M>,
        range: (Bound<K>, Bound<K>),
        cursors: Vec<Cursor<K>>,
    ) -> Self {
        Self {
            map,
            cursors_initialized: true,
            cursors,
            range,
        }
    }

    fn ensure_cursors_initialized(&mut self) {
        if self.cursors_initialized {
            return;
        }

        match self.range.start_bound() {
            Bound::Unbounded => {
                self.cursors.push(Cursor::Address(self.map.root_addr));
            }
            Bound::Included(key) | Bound::Excluded(key) => {
                let mut node = self.map.load_node(self.map.root_addr);
                loop {
                    match node.search(key) {
                        Ok(idx) => {
                            if let Bound::Included(_) = self.range.start_bound() {
                                // We found the key exactly matching the left bound.
                                // Here is where we'll start the iteration.
                                self.cursors.push(Cursor::Node {
                                    node,
                                    next: Index::Entry(idx),
                                });
                                break;
                            } else {
                                // We found the key that we must
                                // exclude.  We add its right neighbor
                                // to the stack and start iterating
                                // from its right child.
                                let right_child = match node.node_type() {
                                    NodeType::Internal => Some(node.child(idx + 1)),
                                    NodeType::Leaf => None,
                                };

                                if idx + 1 != node.entries_len()
                                    && self.range.contains(node.key(idx + 1))
                                {
                                    self.cursors.push(Cursor::Node {
                                        node,
                                        next: Index::Entry(idx + 1),
                                    });
                                }
                                if let Some(right_child) = right_child {
                                    self.cursors.push(Cursor::Address(right_child));
                                }
                                break;
                            }
                        }
                        Err(idx) => {
                            // The `idx` variable points to the first
                            // key that is greater than the left
                            // bound.
                            //
                            // If the index points to a valid node, we
                            // will visit its left subtree and then
                            // return to this key.
                            //
                            // If the index points at the end of
                            // array, we'll continue with the right
                            // child of the last key.

                            // Load the left child of the node to visit if it exists.
                            // This is done first to avoid cloning the node.
                            let child = match node.node_type() {
                                NodeType::Internal => {
                                    // Note that loading a child node cannot fail since
                                    // len(children) = len(entries) + 1
                                    Some(self.map.load_node(node.child(idx)))
                                }
                                NodeType::Leaf => None,
                            };

                            if idx < node.entries_len() && self.range.contains(node.key(idx)) {
                                self.cursors.push(Cursor::Node {
                                    node,
                                    next: Index::Entry(idx),
                                });
                            }

                            match child {
                                None => {
                                    // Leaf node. Return an iterator with the found cursors.
                                    break;
                                }
                                Some(child) => {
                                    // Iterate over the child node.
                                    node = child;
                                }
                            }
                        }
                    }
                }
            }
        }
        self.cursors_initialized = true;
    }

    // Iterates to find the next element in the requested range.
    // If it exists, `map` is applied to that element and the result is returned.
    fn next_map<T, F: Fn(&Node<K>, usize) -> T>(&mut self, map: F) -> Option<T> {
        self.ensure_cursors_initialized();

        // If the cursors are empty. Iteration is complete.
        match self.cursors.pop()? {
            Cursor::Address(address) => {
                if address != NULL {
                    // Load the node at the given address, and add it to the cursors.
                    let node = self.map.load_node(address);
                    self.cursors.push(Cursor::Node {
                        next: match node.node_type() {
                            // Iterate on internal nodes starting from the first child.
                            NodeType::Internal => Index::Child(0),
                            // Iterate on leaf nodes starting from the first entry.
                            NodeType::Leaf => Index::Entry(0),
                        },
                        node,
                    });
                }
                self.next_map(map)
            }

            Cursor::Node {
                node,
                next: Index::Child(child_idx),
            } => {
                let child_address = node.child(child_idx);

                // After iterating on the child, iterate on the next _entry_ in this node.
                // The entry immediately after the child has the same index as the child's.
                self.cursors.push(Cursor::Node {
                    node,
                    next: Index::Entry(child_idx),
                });

                // Add the child to the top of the cursors to be iterated on first.
                self.cursors.push(Cursor::Address(child_address));

                self.next_map(map)
            }

            Cursor::Node {
                node,
                next: Index::Entry(entry_idx),
            } => {
                if entry_idx >= node.entries_len() {
                    // No more entries to iterate on in this node.
                    return self.next_map(map);
                }

                // If the key does not belong to the range, iteration stops.
                if !self.range.contains(node.key(entry_idx)) {
                    // Clear all cursors to avoid needless work in subsequent calls.
                    self.cursors = vec![];
                    return None;
                }

                let res = map(&node, entry_idx);

                // Add to the cursors the next element to be traversed.
                self.cursors.push(Cursor::Node {
                    next: match node.node_type() {
                        // If this is an internal node, add the next child to the cursors.
                        NodeType::Internal => Index::Child(entry_idx + 1),
                        // If this is a leaf node, add the next entry to the cursors.
                        NodeType::Leaf => Index::Entry(entry_idx + 1),
                    },
                    node,
                });

                Some(res)
            }
        }
    }
}

impl<K, V, M> Iterator for Iter<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.next_map(|node, entry_idx| {
            let (key, encoded_value) = node.entry(entry_idx, self.map.memory());
            (key, V::from_bytes(Cow::Owned(encoded_value)))
        })
    }

    fn count(mut self) -> usize
    where
        Self: Sized,
    {
        let mut cnt = 0;
        while self.next_map(|_, _| ()).is_some() {
            cnt += 1;
        }
        cnt
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn iterate_leaf() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        for i in 0..10u8 {
            btree.insert(i, i + 1);
        }

        let mut i = 0;
        for (key, value) in btree.iter() {
            assert_eq!(key, i);
            assert_eq!(value, i + 1);
            i += 1;
        }

        assert_eq!(i, 10u8);
    }

    #[test]
    fn iterate_children() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        // Iteration should be in ascending order.
        let mut i = 0;
        for (key, value) in btree.iter() {
            assert_eq!(key, i);
            assert_eq!(value, i + 1);
            i += 1;
        }

        assert_eq!(i, 100);
    }
}
