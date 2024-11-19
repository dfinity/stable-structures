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
pub(crate) struct IterInternal<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    // A reference to the map being iterated on.
    map: &'a BTreeMap<K, V, M>,

    // Flags indicating if the cursors have been initialized yet. These are needed to distinguish
    // between the case where the iteration hasn't started yet and the case where the iteration has
    // finished (in both cases the cursors will be empty).
    forward_cursors_initialized: bool,
    backward_cursors_initialized: bool,

    // Stacks of cursors indicating the current iteration positions in the tree.
    forward_cursors: Vec<Cursor<K>>,
    backward_cursors: Vec<Cursor<K>>,

    // The range of keys we want to traverse.
    range: (Bound<K>, Bound<K>),
}

impl<'a, K, V, M> IterInternal<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    pub(crate) fn new(map: &'a BTreeMap<K, V, M>) -> Self {
        Self {
            map,
            forward_cursors_initialized: false,
            backward_cursors_initialized: false,
            forward_cursors: vec![],
            backward_cursors: vec![],
            range: (Bound::Unbounded, Bound::Unbounded),
        }
    }

    /// Returns an empty iterator.
    pub(crate) fn null(map: &'a BTreeMap<K, V, M>) -> Self {
        Self {
            map,
            forward_cursors_initialized: true,
            backward_cursors_initialized: true,
            forward_cursors: vec![],
            backward_cursors: vec![],
            range: (Bound::Unbounded, Bound::Unbounded),
        }
    }

    pub(crate) fn new_in_range(map: &'a BTreeMap<K, V, M>, range: (Bound<K>, Bound<K>)) -> Self {
        Self {
            map,
            forward_cursors_initialized: false,
            backward_cursors_initialized: false,
            forward_cursors: vec![],
            backward_cursors: vec![],
            range,
        }
    }

    fn initialize_forward_cursors(&mut self) {
        debug_assert!(!self.forward_cursors_initialized);

        match self.range.start_bound() {
            Bound::Unbounded => {
                self.forward_cursors
                    .push(Cursor::Address(self.map.root_addr));
            }
            Bound::Included(key) | Bound::Excluded(key) => {
                let mut node = self.map.load_node(self.map.root_addr);
                loop {
                    match node.search(key) {
                        Ok(idx) => {
                            if let Bound::Included(_) = self.range.start_bound() {
                                // We found the key exactly matching the left bound.
                                // Here is where we'll start the iteration.
                                self.forward_cursors.push(Cursor::Node {
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

                                if idx + 1 < node.entries_len()
                                    && self.range.contains(node.key(idx + 1))
                                {
                                    self.forward_cursors.push(Cursor::Node {
                                        node,
                                        next: Index::Entry(idx + 1),
                                    });
                                }
                                if let Some(right_child) = right_child {
                                    self.forward_cursors.push(Cursor::Address(right_child));
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
                                self.forward_cursors.push(Cursor::Node {
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
        self.forward_cursors_initialized = true;
    }

    fn initialize_backward_cursors(&mut self) {
        debug_assert!(!self.backward_cursors_initialized);

        match self.range.end_bound() {
            Bound::Unbounded => {
                self.backward_cursors
                    .push(Cursor::Address(self.map.root_addr));
            }
            Bound::Included(key) | Bound::Excluded(key) => {
                let mut node = self.map.load_node(self.map.root_addr);
                loop {
                    match node.search(key) {
                        Ok(idx) => {
                            if let Bound::Included(_) = self.range.end_bound() {
                                // We found the key exactly matching the right bound.
                                // Here is where we'll start the iteration.
                                self.backward_cursors.push(Cursor::Node {
                                    node,
                                    next: Index::Entry(idx),
                                });
                                break;
                            } else {
                                // We found the key that we must
                                // exclude. We add its left neighbor
                                // to the stack and start iterating
                                // from its left child.
                                let left_child = match node.node_type() {
                                    NodeType::Internal => Some(node.child(idx)),
                                    NodeType::Leaf => None,
                                };

                                if idx > 0 && self.range.contains(node.key(idx - 1)) {
                                    self.backward_cursors.push(Cursor::Node {
                                        node,
                                        next: Index::Entry(idx - 1),
                                    });
                                }
                                if let Some(left_child) = left_child {
                                    self.backward_cursors.push(Cursor::Address(left_child));
                                }
                                break;
                            }
                        }
                        Err(idx) => {
                            // The `idx` variable points to the first
                            // key that is greater than the right
                            // bound.
                            //
                            // If the index points to a valid node, we
                            // will visit its left subtree.
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

                            if idx > 0 && self.range.contains(node.key(idx - 1)) {
                                self.backward_cursors.push(Cursor::Node {
                                    node,
                                    next: Index::Entry(idx - 1),
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
        self.backward_cursors_initialized = true;
    }

    // Iterates to find the next element in the requested range.
    // If it exists, `map` is applied to that element and the result is returned.
    fn next_map<T, F: Fn(&Node<K>, usize) -> T>(&mut self, map: F) -> Option<T> {
        if !self.forward_cursors_initialized {
            self.initialize_forward_cursors();
        }

        // If the cursors are empty. Iteration is complete.
        match self.forward_cursors.pop()? {
            Cursor::Address(address) => {
                if address != NULL {
                    // Load the node at the given address, and add it to the cursors.
                    let node = self.map.load_node(address);
                    self.forward_cursors.push(Cursor::Node {
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

                if child_idx < node.entries_len() {
                    // After iterating on the child, iterate on the next _entry_ in this node.
                    // The entry immediately after the child has the same index as the child's.
                    self.forward_cursors.push(Cursor::Node {
                        node,
                        next: Index::Entry(child_idx),
                    });
                }

                // Add the child to the top of the cursors to be iterated on first.
                self.forward_cursors.push(Cursor::Address(child_address));

                self.next_map(map)
            }

            Cursor::Node {
                node,
                next: Index::Entry(entry_idx),
            } => {
                // If the key does not belong to the range, iteration stops.
                if !self.range.contains(node.key(entry_idx)) {
                    // Clear all cursors to avoid needless work in subsequent calls.
                    self.forward_cursors = vec![];
                    self.backward_cursors = vec![];
                    return None;
                }

                let res = map(&node, entry_idx);
                self.range.0 = Bound::Excluded(node.key(entry_idx).clone());

                let next = match node.node_type() {
                    // If this is an internal node, add the next child to the cursors.
                    NodeType::Internal => Index::Child(entry_idx + 1),
                    // If this is a leaf node, and it contains another entry, add the
                    // next entry to the cursors.
                    NodeType::Leaf if entry_idx + 1 < node.entries_len() => {
                        Index::Entry(entry_idx + 1)
                    }
                    _ => return Some(res),
                };

                // Add to the cursors the next element to be traversed.
                self.forward_cursors.push(Cursor::Node { next, node });
                Some(res)
            }
        }
    }

    // Iterates to find the next back element in the requested range.
    // If it exists, `map` is applied to that element and the result is returned.
    fn next_back_map<T, F: Fn(&Node<K>, usize) -> T>(&mut self, map: F) -> Option<T> {
        if !self.backward_cursors_initialized {
            self.initialize_backward_cursors();
        }

        // If the cursors are empty. Iteration is complete.
        match self.backward_cursors.pop()? {
            Cursor::Address(address) => {
                if address != NULL {
                    // Load the node at the given address, and add it to the cursors.
                    let node = self.map.load_node(address);
                    if let Some(next) = match node.node_type() {
                        // Iterate on internal nodes starting from the last child.
                        NodeType::Internal if node.children_len() > 0 => {
                            Some(Index::Child(node.children_len() - 1))
                        }
                        // Iterate on leaf nodes starting from the last entry.
                        NodeType::Leaf if node.entries_len() > 0 => {
                            Some(Index::Entry(node.entries_len() - 1))
                        }
                        _ => None,
                    } {
                        self.backward_cursors.push(Cursor::Node { next, node });
                    }
                }
                self.next_back_map(map)
            }

            Cursor::Node {
                node,
                next: Index::Child(child_idx),
            } => {
                let child_address = node.child(child_idx);

                if 0 < child_idx {
                    // After iterating on the child, iterate on the previous _entry_ in this node.
                    self.backward_cursors.push(Cursor::Node {
                        node,
                        next: Index::Entry(child_idx - 1),
                    });
                }

                // Add the child to the top of the cursors to be iterated on first.
                self.backward_cursors.push(Cursor::Address(child_address));

                self.next_back_map(map)
            }

            Cursor::Node {
                node,
                next: Index::Entry(entry_idx),
            } => {
                // If the key does not belong to the range, iteration stops.
                if !self.range.contains(node.key(entry_idx)) {
                    // Clear all cursors to avoid needless work in subsequent calls.
                    self.forward_cursors = vec![];
                    self.backward_cursors = vec![];
                    return None;
                }

                let res = map(&node, entry_idx);
                self.range.1 = Bound::Excluded(node.key(entry_idx).clone());

                if let Some(next) = match node.node_type() {
                    // If this is an internal node, add the previous child to the cursors.
                    NodeType::Internal => Some(Index::Child(entry_idx)),
                    // If this is a leaf node, add the previous entry to the cursors.
                    NodeType::Leaf if entry_idx > 0 => Some(Index::Entry(entry_idx - 1)),
                    _ => None,
                } {
                    // Add to the cursors the next element to be traversed.
                    self.backward_cursors.push(Cursor::Node { next, node });
                }

                Some(res)
            }
        }
    }

    fn count(&mut self) -> usize {
        let mut cnt = 0;
        while self.next_map(|_, _| ()).is_some() {
            cnt += 1;
        }
        cnt
    }
}

pub struct Iter<'a, K, V, M>(IterInternal<'a, K, V, M>)
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory;

impl<K, V, M> Iterator for Iter<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next_map(|node, entry_idx| {
            let (key, encoded_value) = node.entry(entry_idx, self.0.map.memory());
            (key.clone(), V::from_bytes(Cow::Borrowed(encoded_value)))
        })
    }

    fn count(mut self) -> usize
    where
        Self: Sized,
    {
        self.0.count()
    }
}

impl<K, V, M> DoubleEndedIterator for Iter<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back_map(|node, entry_idx| {
            let (key, encoded_value) = node.entry(entry_idx, self.0.map.memory());
            (key.clone(), V::from_bytes(Cow::Borrowed(encoded_value)))
        })
    }
}

pub struct KeysIter<'a, K, V, M>(IterInternal<'a, K, V, M>)
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory;

impl<K, V, M> Iterator for KeysIter<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next_map(|node, entry_idx| node.key(entry_idx).clone())
    }

    fn count(mut self) -> usize
    where
        Self: Sized,
    {
        self.0.count()
    }
}

impl<K, V, M> DoubleEndedIterator for KeysIter<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0
            .next_back_map(|node, entry_idx| node.key(entry_idx).clone())
    }
}

pub struct ValuesIter<'a, K, V, M>(IterInternal<'a, K, V, M>)
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory;

impl<K, V, M> Iterator for ValuesIter<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next_map(|node, entry_idx| {
            let encoded_value = node.value(entry_idx, self.0.map.memory());
            V::from_bytes(Cow::Borrowed(encoded_value))
        })
    }

    fn count(mut self) -> usize
    where
        Self: Sized,
    {
        self.0.count()
    }
}

impl<K, V, M> DoubleEndedIterator for ValuesIter<'_, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back_map(|node, entry_idx| {
            let encoded_value = node.value(entry_idx, self.0.map.memory());
            V::from_bytes(Cow::Borrowed(encoded_value))
        })
    }
}

impl<'a, K, V, M> From<IterInternal<'a, K, V, M>> for Iter<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    fn from(value: IterInternal<'a, K, V, M>) -> Self {
        Iter(value)
    }
}

impl<'a, K, V, M> From<IterInternal<'a, K, V, M>> for KeysIter<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    fn from(value: IterInternal<'a, K, V, M>) -> Self {
        KeysIter(value)
    }
}

impl<'a, K, V, M> From<IterInternal<'a, K, V, M>> for ValuesIter<'a, K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    fn from(value: IterInternal<'a, K, V, M>) -> Self {
        ValuesIter(value)
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

    #[test]
    fn iterate_range() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        // Iteration should be in ascending order.
        let mut i = 10;
        for (key, value) in btree.range(10..90) {
            assert_eq!(key, i);
            assert_eq!(value, i + 1);
            i += 1;
        }

        assert_eq!(i, 90);
    }

    #[test]
    fn iterate_reverse() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        // Iteration should be in descending order.
        let mut i = 100;
        for (key, value) in btree.iter().rev() {
            i -= 1;
            assert_eq!(key, i);
            assert_eq!(value, i + 1);
        }

        assert_eq!(i, 0);
    }

    #[test]
    fn iterate_range_reverse() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        // Iteration should be in descending order.
        let mut i = 80;
        for (key, value) in btree.range(20..80).rev() {
            i -= 1;
            assert_eq!(key, i);
            assert_eq!(value, i + 1);
        }

        assert_eq!(i, 20);
    }

    #[test]
    fn iterate_from_both_ends() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        let mut iter = btree.iter();

        for i in 0..50 {
            let (key, value) = iter.next().unwrap();
            assert_eq!(key, i);
            assert_eq!(value, i + 1);

            let (key, value) = iter.next_back().unwrap();
            assert_eq!(key, 99 - i);
            assert_eq!(value, 100 - i);
        }

        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn iterate_range_from_both_ends() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        let mut iter = btree.range(30..70);

        for i in 0..20 {
            let (key, value) = iter.next().unwrap();
            assert_eq!(key, 30 + i);
            assert_eq!(value, 31 + i);

            let (key, value) = iter.next_back().unwrap();
            assert_eq!(key, 69 - i);
            assert_eq!(value, 70 - i);
        }

        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn keys_from_both_ends() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        let mut iter = btree.keys();

        for i in 0..50 {
            let key = iter.next().unwrap();
            assert_eq!(key, i);

            let key = iter.next_back().unwrap();
            assert_eq!(key, 99 - i);
        }

        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn keys_range_from_both_ends() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        let mut iter = btree.keys_range(30..70);

        for i in 0..20 {
            let key = iter.next().unwrap();
            assert_eq!(key, 30 + i);

            let key = iter.next_back().unwrap();
            assert_eq!(key, 69 - i);
        }

        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn values_from_both_ends() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        let mut iter = btree.values();

        for i in 0..50 {
            let value = iter.next().unwrap();
            assert_eq!(value, i + 1);

            let value = iter.next_back().unwrap();
            assert_eq!(value, 100 - i);
        }

        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn values_range_from_both_ends() {
        let mem = make_memory();
        let mut btree = BTreeMap::new(mem);

        // Insert the elements in reverse order.
        for i in (0..100u64).rev() {
            btree.insert(i, i + 1);
        }

        let mut iter = btree.values_range(30..70);

        for i in 0..20 {
            let value = iter.next().unwrap();
            assert_eq!(value, 31 + i);

            let value = iter.next_back().unwrap();
            assert_eq!(value, 70 - i);
        }

        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }
}
