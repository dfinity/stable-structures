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
        self.cache.borrow().get(&address).cloned().inspect(|_| {
            self.touch(address);
        })
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
