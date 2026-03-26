use crate::btreemap::node::{Node, NodeType};
use crate::{BTreeMap, Memory, Storable};
use std::borrow::Cow;

pub enum Entry<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> {
    Vacant(VacantEntry<'a, K, V, M>),
    Occupied(OccupiedEntry<'a, K, V, M>),
}

pub struct VacantEntry<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> {
    pub(crate) map: &'a mut BTreeMap<K, V, M>,
    pub(crate) key: K,
    pub(crate) node: Node<K>,
    pub(crate) idx: usize,
}

pub struct OccupiedEntry<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> {
    pub(crate) map: &'a mut BTreeMap<K, V, M>,
    pub(crate) key: K,
    pub(crate) node: Node<K>,
    pub(crate) idx: usize,
}

impl<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> Entry<'a, K, V, M> {
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    pub fn into_key(self) -> K {
        match self {
            Entry::Occupied(entry) => entry.into_key(),
            Entry::Vacant(entry) => entry.into_key(),
        }
    }
}

impl<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> VacantEntry<'a, K, V, M> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn into_key(self) -> K {
        self.key
    }

    pub fn insert(mut self, value: V) {
        self.node
            .insert_entry(self.idx, (self.key, value.into_bytes_checked()));

        self.map.save_node(&mut self.node);
        self.map.length += 1;
        self.map.save_header();
    }
}

impl<'a, K: 'a + Storable + Ord + Clone, V: 'a + Storable, M: Memory> OccupiedEntry<'a, K, V, M> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn into_key(self) -> K {
        self.key
    }

    pub fn get(&self) -> V {
        let value_bytes = self.node.value(self.idx, self.map.memory());
        V::from_bytes(Cow::Borrowed(value_bytes))
    }

    pub fn insert(mut self, value: V) {
        self.map
            .update_value(&mut self.node, self.idx, value.into_bytes_checked());
    }

    pub fn remove(self) {
        if self.node.can_remove_entry_without_merging() {
            match self.node.node_type() {
                NodeType::Leaf => self.map.remove_from_leaf_node(self.node, self.idx),
                NodeType::Internal => self
                    .map
                    .remove_from_internal_node(self.node, self.idx, &self.key),
            };
        } else {
            // TODO avoid using this slow path
            let root = self.map.load_node(self.map.root_addr);
            self.map.remove_helper(root, &self.key);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn entry_end_to_end() {
        let mut map = BTreeMap::new(Rc::new(RefCell::new(Vec::new())));

        for i in 0u32..100 {
            let Entry::Vacant(e) = map.entry(i) else {
                panic!();
            };
            e.insert(i);
        }

        for i in 0u32..100 {
            let Entry::Occupied(e) = map.entry(i) else {
                panic!();
            };
            assert_eq!(i, e.get());
            e.insert(i + 1);
        }

        for i in 0u32..100 {
            let Entry::Occupied(e) = map.entry(i) else {
                panic!();
            };
            assert_eq!(i + 1, e.get());
            e.remove();
        }

        assert!(map.is_empty());
    }
}
