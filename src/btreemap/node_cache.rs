use crate::btreemap::node::Node;
use crate::{types::Address, Storable};
use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct Counter(u64);

/// Cache with LRU tracking.
#[derive(Debug)]
pub struct NodeCache<K>
where
    K: Storable + Ord + Clone,
{
    cache: RefCell<BTreeMap<Address, Node<K>>>,
    capacity: usize,
    counter: RefCell<Counter>,
    lru_order: RefCell<BTreeMap<Counter, Address>>,
    usage: RefCell<BTreeMap<Address, Counter>>,
    stats: RefCell<(u32, u32)>, // (hits, misses)
}

impl<K> NodeCache<K>
where
    K: Storable + Ord + Clone,
{
    /// New cache with given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: RefCell::new(BTreeMap::new()),
            capacity,
            counter: RefCell::new(Counter(0)),
            lru_order: RefCell::new(BTreeMap::new()),
            usage: RefCell::new(BTreeMap::new()),
            stats: RefCell::new((0, 0)),
        }
    }

    /// Clear the cache.
    pub fn clear(&self) {
        self.cache.borrow_mut().clear();
        self.lru_order.borrow_mut().clear();
        self.usage.borrow_mut().clear();
        *self.counter.borrow_mut() = Counter(0);
    }

    /// Read node and update LRU order.
    pub fn read_node(&self, address: Address) -> Option<Node<K>> {
        if self.capacity == 0 {
            return None;
        }

        let mut stats = self.stats.borrow_mut();
        match self.cache.borrow().get(&address).cloned() {
            Some(node) => {
                self.touch(address);
                stats.0 += 1; // Increment hits.
                Some(node)
            }
            None => {
                stats.1 += 1; // Increment misses.
                None
            }
        }
    }

    /// Write node; evict LRU if full.
    pub fn write_node(&self, address: Address, node: Node<K>) {
        if self.capacity == 0 {
            return;
        }

        {
            let mut cache = self.cache.borrow_mut();
            if cache.len() >= self.capacity {
                let mut lru_order = self.lru_order.borrow_mut();
                if let Some((&old_ctr, &lru_addr)) = lru_order.iter().next() {
                    lru_order.remove(&old_ctr);
                    cache.remove(&lru_addr);
                    self.usage.borrow_mut().remove(&lru_addr);
                }
            }
            cache.insert(address, node);
        }
        self.touch(address);
    }

    /// Remove node.
    pub fn remove_node(&self, address: Address) {
        if self.capacity == 0 {
            return;
        }

        self.cache.borrow_mut().remove(&address);
        if let Some(old_ctr) = self.usage.borrow_mut().remove(&address) {
            self.lru_order.borrow_mut().remove(&old_ctr);
        }
    }

    /// Update LRU order by assigning a new counter.
    fn touch(&self, address: Address) {
        let new_counter = {
            let mut counter = self.counter.borrow_mut();
            counter.0 += 1;
            *counter
        };
        let mut usage = self.usage.borrow_mut();
        let mut lru_order = self.lru_order.borrow_mut();
        if let Some(old_counter) = usage.insert(address, new_counter) {
            lru_order.remove(&old_counter);
        }
        lru_order.insert(new_counter, address);
    }
}

impl<K> Drop for NodeCache<K>
where
    K: Storable + Ord + Clone,
{
    fn drop(&mut self) {
        // cargo test -- --nocapture > ./tmp/output.txt 2>&1
        let stats = self.stats.borrow();
        let msg = format!(
            "\nNodeCache: hits: {} ({:>5.1} %), misses: {}, total: {}",
            stats.0,
            (stats.0 as f64 / (stats.0 + stats.1).max(1) as f64) * 100.0,
            stats.1,
            stats.0 + stats.1,
        );
        crate::debug::print(msg);
    }
}
