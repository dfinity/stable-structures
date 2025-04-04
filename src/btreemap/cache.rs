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

/// Cache with eviction policy that minimizes duplication of keys and values.
#[derive(Debug, Default)]
pub struct Cache<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    /// Main storage mapping from internal id to value.
    cache: RefCell<BTreeMap<K, V>>,
    capacity: usize,
    counter: RefCell<Counter>,
    /// LRU order mapping: counter -> K.
    lru_order: RefCell<BTreeMap<Counter, K>>,
    /// Usage mapping: K -> counter.
    usage: RefCell<BTreeMap<K, Counter>>,
    stats: RefCell<CacheStats>,
}

impl<K, V> Cache<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    /// Creates a new cache with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: RefCell::new(BTreeMap::new()),
            capacity,
            counter: RefCell::new(Counter(0)),
            lru_order: RefCell::new(BTreeMap::new()),
            usage: RefCell::new(BTreeMap::new()),
            stats: RefCell::new(CacheStats::default()),
        }
    }

    /// Clears the cache.
    pub fn clear(&self) {
        self.cache.borrow_mut().clear();
        self.lru_order.borrow_mut().clear();
        self.usage.borrow_mut().clear();
        *self.counter.borrow_mut() = Counter(0);
        *self.stats.borrow_mut() = CacheStats::default();
    }

    /// Retrieves the value associated with the given key and updates the LRU order.
    pub fn get(&self, key: &K) -> Option<V> {
        if self.capacity == 0 {
            return None;
        }
        if let Some(value) = self.cache.borrow().get(&key) {
            self.touch(key.clone());
            self.stats.borrow_mut().hits += 1;
            return Some(value.clone());
        }
        self.stats.borrow_mut().misses += 1;
        None
    }

    /// Inserts the given key and value; if the cache is full, evicts the least-recently used entry.
    pub fn insert(&self, key: K, value: V) {
        if self.capacity == 0 {
            return;
        }
        if self.cache.borrow().len() >= self.capacity {
            self.evict_one();
        }
        self.cache.borrow_mut().insert(key.clone(), value);
        self.touch(key);
    }

    /// Removes the entry associated with the given key.
    pub fn remove(&self, key: &K) {
        if self.capacity == 0 {
            return;
        }
        self.cache.borrow_mut().remove(key);
        if let Some(old_counter) = self.usage.borrow_mut().remove(key) {
            self.lru_order.borrow_mut().remove(&old_counter);
        }
    }

    /// Returns the current number of entries in the cache.
    pub fn len(&self) -> usize {
        self.cache.borrow().len()
    }

    /// Returns the cache's capacity.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Sets a new capacity for the cache, evicting entries if necessary.
    pub fn set_capacity(&mut self, capacity: usize) {
        self.capacity = capacity;
        if self.capacity == 0 {
            self.clear();
        } else {
            while self.cache.borrow().len() > self.capacity {
                self.evict_one();
            }
        }
    }

    /// Evicts a single entry based on the LRU policy.
    fn evict_one(&self) -> bool {
        let mut lru_order = self.lru_order.borrow_mut();
        if let Some((&old_counter, key)) = lru_order.iter().next() {
            let key = key.clone();
            lru_order.remove(&old_counter);
            self.cache.borrow_mut().remove(&key);
            self.usage.borrow_mut().remove(&key);
            return true;
        }
        false
    }

    /// Updates the LRU order by assigning a new counter for the given id.
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

    /// Returns the current cache statistics.
    pub fn stats(&self) -> CacheStats {
        *self.stats.borrow()
    }

    /// Resets the cache statistics.
    pub fn reset_stats(&self) {
        *self.stats.borrow_mut() = CacheStats::default();
    }

    /// Returns the current hit ratio.
    pub fn hit_ratio(&self) -> f64 {
        self.stats().hit_ratio()
    }
}
