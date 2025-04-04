use std::cell::RefCell;
use std::collections::BTreeMap;

/// Incrementing counter for tracking the order of usage in the cache.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Default)]
struct Counter(u64);

/// Runtime statistics for the cache.
#[derive(Default, Debug, Copy, Clone)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
}

impl CacheStats {
    /// Returns the number of reads.
    pub fn total(&self) -> u64 {
        self.hits + self.misses
    }

    /// Computes and returns the current hit ratio.
    pub fn hit_ratio(&self) -> f64 {
        self.hits as f64 / self.total().max(1) as f64
    }
}

/// Cache with eviction policy.
#[derive(Debug, Default)]
pub struct Cache<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    cache: RefCell<BTreeMap<K, V>>,
    capacity: usize,
    counter: RefCell<Counter>,
    lru_order: RefCell<BTreeMap<Counter, K>>,
    usage: RefCell<BTreeMap<K, Counter>>,
    stats: RefCell<CacheStats>,
}

impl<K, V> Cache<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    /// New cache with given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: RefCell::new(BTreeMap::new()),
            capacity,
            counter: RefCell::new(Counter::default()),
            lru_order: RefCell::new(BTreeMap::new()),
            usage: RefCell::new(BTreeMap::new()),
            stats: RefCell::new(CacheStats::default()),
        }
    }

    /// Clear the cache.
    pub fn clear(&self) {
        self.cache.borrow_mut().clear();
        self.lru_order.borrow_mut().clear();
        self.usage.borrow_mut().clear();
        *self.counter.borrow_mut() = Counter::default();
        *self.stats.borrow_mut() = CacheStats::default();
    }

    /// Read node and update LRU order.
    pub fn get(&self, key: K) -> Option<V> {
        if self.capacity == 0 {
            return None;
        }

        match self.cache.borrow().get(&key).cloned() {
            Some(node) => {
                self.touch(key);
                self.stats.borrow_mut().hits += 1;
                Some(node)
            }
            None => {
                self.stats.borrow_mut().misses += 1;
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
            self.evict_single_helper(&mut cache);
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

    pub fn len(&self) -> usize {
        self.cache.borrow().len()
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn set_capacity(&mut self, capacity: usize) {
        self.capacity = capacity;
        if self.capacity == 0 {
            self.clear();
        } else {
            let mut cache = self.cache.borrow_mut();
            while cache.len() > self.capacity {
                self.evict_single_helper(&mut cache);
            }
        }
    }

    fn evict_single_helper(&self, cache: &mut BTreeMap<K, V>) -> bool {
        if cache.len() >= self.capacity {
            let mut lru_order = self.lru_order.borrow_mut();
            if let Some((&old_counter, old_key)) = lru_order.iter().next() {
                let old_key = old_key.clone();
                lru_order.remove(&old_counter);
                cache.remove(&old_key);
                self.usage.borrow_mut().remove(&old_key);
                return true;
            }
        }
        false
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

    /// Returns current cache statistics such as hits, misses, etc.
    pub fn stats(&self) -> CacheStats {
        *self.stats.borrow()
    }

    /// Resets the cache statistics (e.g., after a tuning period).
    pub fn reset_stats(&self) {
        *self.stats.borrow_mut() = CacheStats::default();
    }

    /// Computes and returns the current hit ratio.
    pub fn hit_ratio(&self) -> f64 {
        self.stats().hit_ratio()
    }
}
