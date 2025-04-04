use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct Counter(u64);

/// Cache with LRU tracking.
#[derive(Debug)]
pub struct NodeCache<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    cache: RefCell<BTreeMap<K, V>>,
    capacity: usize,
    counter: RefCell<Counter>,
    lru_order: RefCell<BTreeMap<Counter, K>>,
    usage: RefCell<BTreeMap<K, Counter>>,
    stats: RefCell<(u32, u32)>, // (hits, misses)
}

impl<K, V> NodeCache<K, V>
where
    K: Clone + Ord,
    V: Clone,
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
    pub fn get(&self, key: K) -> Option<V> {
        if self.capacity == 0 {
            return None;
        }

        let mut stats = self.stats.borrow_mut();
        match self.cache.borrow().get(&key).cloned() {
            Some(node) => {
                self.touch(key);
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
    pub fn insert(&self, key: K, node: &V) {
        if self.capacity == 0 {
            return;
        }

        {
            let mut cache = self.cache.borrow_mut();
            if cache.len() >= self.capacity {
                let mut lru_order = self.lru_order.borrow_mut();
                if let Some((&old_counter, old_key)) = lru_order.iter().next() {
                    let old_key = old_key.clone();
                    lru_order.remove(&old_counter);
                    cache.remove(&old_key);
                    self.usage.borrow_mut().remove(&old_key);
                }
            }
            cache.insert(key.clone(), node.clone());
        }
        self.touch(key);
    }

    /// Remove node.
    pub fn remove(&self, key: K) {
        if self.capacity == 0 {
            return;
        }

        self.cache.borrow_mut().remove(&key);
        if let Some(old_ctr) = self.usage.borrow_mut().remove(&key) {
            self.lru_order.borrow_mut().remove(&old_ctr);
        }
    }

    /// Update LRU order by assigning a new counter.
    fn touch(&self, key: K) {
        let new_counter = {
            let mut counter = self.counter.borrow_mut();
            counter.0 += 1;
            *counter
        };
        let mut usage = self.usage.borrow_mut();
        let mut lru_order = self.lru_order.borrow_mut();
        if let Some(old_counter) = usage.insert(key.clone(), new_counter) {
            lru_order.remove(&old_counter);
        }
        lru_order.insert(new_counter, key);
    }
}

impl<K, V> Drop for NodeCache<K, V>
where
    K: Clone + Ord,
    V: Clone,
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
