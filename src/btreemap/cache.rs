use std::cell::RefCell;
use std::collections::BTreeMap;

/// A dedicated identifier type for cache entries.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Default)]
struct CacheId(u64);

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
/// Uses `CacheId` as an internal identifier for type safety.
#[derive(Debug, Default)]
pub struct Cache<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    /// Main storage mapping from internal id to value.
    cache: RefCell<BTreeMap<CacheId, V>>,
    /// Mapping from key to internal id.
    key_to_id: RefCell<BTreeMap<K, CacheId>>,
    /// Mapping from internal id back to key.
    id_to_key: RefCell<BTreeMap<CacheId, K>>,
    capacity: usize,
    counter: RefCell<Counter>,
    /// LRU order mapping: counter -> CacheId.
    lru_order: RefCell<BTreeMap<Counter, CacheId>>,
    /// Usage mapping: CacheId -> counter.
    usage: RefCell<BTreeMap<CacheId, Counter>>,
    stats: RefCell<CacheStats>,
    /// Next id generator.
    next_id: RefCell<CacheId>,
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
            key_to_id: RefCell::new(BTreeMap::new()),
            id_to_key: RefCell::new(BTreeMap::new()),
            capacity,
            counter: RefCell::new(Counter(0)),
            lru_order: RefCell::new(BTreeMap::new()),
            usage: RefCell::new(BTreeMap::new()),
            stats: RefCell::new(CacheStats::default()),
            next_id: RefCell::new(CacheId(0)),
        }
    }

    /// Clears the cache.
    pub fn clear(&self) {
        self.cache.borrow_mut().clear();
        self.key_to_id.borrow_mut().clear();
        self.id_to_key.borrow_mut().clear();
        self.lru_order.borrow_mut().clear();
        self.usage.borrow_mut().clear();
        *self.counter.borrow_mut() = Counter(0);
        *self.stats.borrow_mut() = CacheStats::default();
        *self.next_id.borrow_mut() = CacheId(0);
    }

    /// Retrieves the value associated with the given key and updates the LRU order.
    pub fn get(&self, key: &K) -> Option<V> {
        if self.capacity == 0 {
            return None;
        }
        let key_to_id = self.key_to_id.borrow();
        if let Some(&id) = key_to_id.get(key) {
            self.touch(id);
            self.stats.borrow_mut().hits += 1;
            return self.cache.borrow().get(&id).cloned();
        }
        self.stats.borrow_mut().misses += 1;
        None
    }

    /// Inserts the given key and value; if the cache is full, evicts the least-recently used entry.
    pub fn insert(&self, key: K, value: V) {
        if self.capacity == 0 {
            return;
        }
        let mut key_to_id = self.key_to_id.borrow_mut();
        let id = if let Some(&existing_id) = key_to_id.get(&key) {
            // Key already exists: update the value.
            existing_id
        } else {
            // New key: evict if necessary.
            if self.cache.borrow().len() >= self.capacity {
                self.evict_one();
            }
            let new_id = *self.next_id.borrow();
            *self.next_id.borrow_mut() = CacheId(new_id.0 + 1);
            key_to_id.insert(key.clone(), new_id);
            self.id_to_key.borrow_mut().insert(new_id, key.clone());
            new_id
        };
        self.cache.borrow_mut().insert(id, value);
        self.touch(id);
    }

    /// Removes the entry associated with the given key.
    pub fn remove(&self, key: &K) {
        if self.capacity == 0 {
            return;
        }
        if let Some(id) = self.key_to_id.borrow_mut().remove(key) {
            self.cache.borrow_mut().remove(&id);
            self.id_to_key.borrow_mut().remove(&id);
            if let Some(old_ctr) = self.usage.borrow_mut().remove(&id) {
                self.lru_order.borrow_mut().remove(&old_ctr);
            }
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
        if let Some((&old_counter, &id)) = lru_order.iter().next() {
            lru_order.remove(&old_counter);
            self.cache.borrow_mut().remove(&id);
            if let Some(key) = self.id_to_key.borrow_mut().remove(&id) {
                self.key_to_id.borrow_mut().remove(&key);
            }
            self.usage.borrow_mut().remove(&id);
            return true;
        }
        false
    }

    /// Updates the LRU order by assigning a new counter for the given id.
    fn touch(&self, id: CacheId) {
        let new_counter = {
            let mut counter = self.counter.borrow_mut();
            counter.0 += 1;
            *counter
        };
        let mut usage = self.usage.borrow_mut();
        let mut lru_order = self.lru_order.borrow_mut();
        if let Some(old_counter) = usage.insert(id, new_counter) {
            lru_order.remove(&old_counter);
        }
        lru_order.insert(new_counter, id);
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
