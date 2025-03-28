use crate::btreemap::node::Node;
use crate::{types::Address, Storable};
use std::cell::RefCell;
use std::collections::BTreeMap as StdBTreeMap;

/// A node cache with LRU tracking that provides interior mutability.
/// It stores nodes in key-value storage and evicts the least recently used node when full.
/// This implementation uses a counter-based approach so that updating (touching) a key is O(log n).
#[derive(Debug)]
pub struct NodeCache<K>
where
    K: Storable + Ord + Clone,
{
    cache: RefCell<StdBTreeMap<Address, Node<K>>>,
    capacity: usize,
    /// Global counter that increases on each access.
    counter: RefCell<u64>,
    /// Maps usage counters to addresses. The smallest counter is the least recently used.
    lru_order: RefCell<StdBTreeMap<u64, Address>>,
    /// Maps addresses to their current usage counter.
    usage: RefCell<StdBTreeMap<Address, u64>>,
}

impl<K> NodeCache<K>
where
    K: Storable + Ord + Clone,
{
    /// Creates a new NodeCache with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: RefCell::new(StdBTreeMap::new()),
            capacity,
            counter: RefCell::new(0),
            lru_order: RefCell::new(StdBTreeMap::new()),
            usage: RefCell::new(StdBTreeMap::new()),
        }
    }

    /// Returns a cloned node from the cache for the given address, if it exists.
    /// Updates the LRU order if the node is found.
    pub fn read_node(&self, address: Address) -> Option<Node<K>> {
        let result = self.cache.borrow().get(&address).cloned();
        if result.is_some() {
            self.touch(address);
        }
        result
    }

    /// Inserts a node into the cache, evicting the least recently used node if capacity is exceeded.
    pub fn write_node(&self, address: Address, node: Node<K>) {
        {
            let mut cache = self.cache.borrow_mut();
            if cache.len() >= self.capacity {
                // Evict the least recently used node.
                let mut lru_order = self.lru_order.borrow_mut();
                if let Some((&old_counter, &lru_address)) = lru_order.iter().next() {
                    lru_order.remove(&old_counter);
                    cache.remove(&lru_address);
                    self.usage.borrow_mut().remove(&lru_address);
                }
            }
            cache.insert(address, node);
        }
        self.touch(address);
    }

    /// Removes the node associated with the given address from the cache.
    pub fn remove_node(&self, address: Address) {
        self.cache.borrow_mut().remove(&address);
        if let Some(old_counter) = self.usage.borrow_mut().remove(&address) {
            self.lru_order.borrow_mut().remove(&old_counter);
        }
    }

    /// Updates the LRU order for the given address by assigning a new usage counter.
    fn touch(&self, address: Address) {
        let mut counter = self.counter.borrow_mut();
        *counter += 1;
        let new_counter = *counter;

        let mut usage = self.usage.borrow_mut();
        let mut lru_order = self.lru_order.borrow_mut();

        // Remove previous counter value if it exists.
        if let Some(old_counter) = usage.insert(address, new_counter) {
            lru_order.remove(&old_counter);
        }
        lru_order.insert(new_counter, address);
    }
}
