use super::{
    node::{Node, NodeType},
    BTreeMap,
};
use crate::{types::NULL, Address, BoundedStorable, Memory};
use std::borrow::Cow;
use std::ops::{Bound, RangeBounds};

/// An indicator of the current position in the map.
pub(crate) enum Cursor<K: BoundedStorable + Ord + Clone> {
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
    K: BoundedStorable + Ord + Clone,
    V: BoundedStorable,
    M: Memory,
{
    // A reference to the map being iterated on.
    map: &'a BTreeMap<K, V, M>,

    // A stack of cursors indicating the current position in the tree.
    cursors: Vec<Cursor<K>>,

    // The range of keys we want to traverse.
    range: (Bound<K>, Bound<K>),
}

impl<'a, K, V, M> Iter<'a, K, V, M>
where
    K: BoundedStorable + Ord + Clone,
    V: BoundedStorable,
    M: Memory,
{
    pub(crate) fn new(map: &'a BTreeMap<K, V, M>) -> Self {
        Self {
            map,
            // Initialize the cursors with the address of the root of the map.
            cursors: vec![Cursor::Address(map.root_addr)],
            range: (Bound::Unbounded, Bound::Unbounded),
        }
    }

    /// Returns an empty iterator.
    pub(crate) fn null(map: &'a BTreeMap<K, V, M>) -> Self {
        Self {
            map,
            cursors: vec![],
            range: (Bound::Unbounded, Bound::Unbounded),
        }
    }

    pub(crate) fn new_in_range(
        map: &'a BTreeMap<K, V, M>,
        range: (Bound<K>, Bound<K>),
        cursors: Vec<Cursor<K>>,
    ) -> Self {
        Self {
            map,
            cursors,
            range,
        }
    }
}

impl<K, V, M> Iterator for Iter<'_, K, V, M>
where
    K: BoundedStorable + Ord + Clone,
    V: BoundedStorable,
    M: Memory,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        match self.cursors.pop() {
            Some(Cursor::Address(address)) => {
                if address != NULL {
                    // Load the node at the given address, and add it to the cursors.
                    let node = self.map.load_node(address);
                    self.cursors.push(Cursor::Node {
                        next: match node.node_type {
                            // Iterate on internal nodes starting from the first child.
                            NodeType::Internal => Index::Child(0),
                            // Iterate on leaf nodes starting from the first entry.
                            NodeType::Leaf => Index::Entry(0),
                        },
                        node,
                    });
                }
                self.next()
            }

            Some(Cursor::Node {
                node,
                next: Index::Child(child_idx),
            }) => {
                let child_address = *node
                    .children
                    .get(child_idx)
                    .expect("Iterating over children went out of bounds.");

                // After iterating on the child, iterate on the next _entry_ in this node.
                // The entry immediately after the child has the same index as the child's.
                self.cursors.push(Cursor::Node {
                    node,
                    next: Index::Entry(child_idx),
                });

                // Add the child to the top of the cursors to be iterated on first.
                self.cursors.push(Cursor::Address(child_address));

                self.next()
            }

            Some(Cursor::Node {
                node,
                next: Index::Entry(entry_idx),
            }) => {
                if entry_idx >= node.keys.len() {
                    // No more entries to iterate on in this node.
                    return self.next();
                }

                let (key, encoded_value) = node.entry(entry_idx);

                // Add to the cursors the next element to be traversed.
                self.cursors.push(Cursor::Node {
                    next: match node.node_type {
                        // If this is an internal node, add the next child to the cursors.
                        NodeType::Internal => Index::Child(entry_idx + 1),
                        // If this is a leaf node, add the next entry to the cursors.
                        NodeType::Leaf => Index::Entry(entry_idx + 1),
                    },
                    node,
                });

                // If the key does not belong to the range, iteration stops.
                if !self.range.contains(&key) {
                    // Clear all cursors to avoid needless work in subsequent calls.
                    self.cursors = vec![];
                    return None;
                }

                Some((key, V::from_bytes(Cow::Owned(encoded_value))))
            }
            None => {
                // The cursors are empty. Iteration is complete.
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::btreemap::node::CAPACITY;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn iterate_leaf() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        for i in 0..CAPACITY as u8 {
            btree.insert(i, i + 1).unwrap();
        }

        let mut i = 0;
        for (key, value) in btree.iter() {
            assert_eq!(key, i);
            assert_eq!(value, i + 1);
            i += 1;
        }

        assert_eq!(i, CAPACITY as u8);
    }

    #[test]
    fn iterate_children() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1).unwrap();
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
