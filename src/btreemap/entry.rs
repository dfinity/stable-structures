use crate::btreemap::node::{Node, NodeType};
use crate::{BTreeMap, Memory, Storable};
use std::cell::Cell;

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
    pub(crate) cached_value: Cell<Option<V>>,
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

    pub fn and_modify(self, f: impl FnOnce(&mut V)) -> Self {
        match self {
            Entry::Occupied(entry) => Entry::Occupied(entry.and_modify(f)),
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    pub fn or_insert(self, default: V) -> OccupiedEntry<'a, K, V, M> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> OccupiedEntry<'a, K, V, M> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    pub fn or_default(self) -> OccupiedEntry<'a, K, V, M>
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(Default::default()),
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

    pub fn insert(mut self, value: V) -> OccupiedEntry<'a, K, V, M> {
        self.node.insert_entry(
            self.idx,
            (self.key.clone(), value.to_bytes_checked().into_owned()),
        );

        self.map.save_node(&mut self.node);
        self.map.length += 1;
        self.map.save_header();

        OccupiedEntry {
            map: self.map,
            key: self.key,
            node: self.node,
            idx: self.idx,
            cached_value: Cell::new(Some(value)),
        }
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
        if let Some(cached) = self.cached_value.take() {
            cached
        } else {
            self.get()
        }
    }

    pub fn and_modify(mut self, f: impl FnOnce(&mut V)) -> Self {
        let mut value = self.get();
        f(&mut value);
        self.map.update_value(
            &mut self.node,
            self.idx,
            value.to_bytes_checked().into_owned(),
        );
        self
    }

    pub fn insert(mut self, value: V) {
        self.map
            .update_value(&mut self.node, self.idx, value.into_bytes_checked());
    }

    pub fn remove(self) {
        match self.node.node_type() {
            NodeType::Leaf if self.node.can_remove_entry_without_merging() => {
                self.map.remove_from_leaf_node(self.node, self.idx);
            }
            NodeType::Leaf => {
                // TODO avoid using this slow path
                let root = self.map.load_node(self.map.root_addr);
                self.map.remove_helper(root, &self.key);
            }
            NodeType::Internal => {
                self.map
                    .remove_from_internal_node(self.node, self.idx, &self.key);
            }
        };
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
