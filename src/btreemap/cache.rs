use std::collections::BTreeMap;

#[allow(non_upper_case_globals)]
const KiB: usize = 1024;
#[allow(non_upper_case_globals)]
const MiB: usize = 1024 * KiB;
#[allow(non_upper_case_globals)]
const GiB: usize = 1024 * MiB;

const DEFAULT_SIZE_LIMIT: usize = 3 * GiB;

pub trait ByteSize {
    fn byte_size(&self) -> usize {
        std::mem::size_of_val(self)
    }
}

/// Incrementing counter for tracking the order of usage in the cache.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Default)]
struct Counter(u64);

/// Runtime statistics for the cache.
#[derive(Default, Debug, Copy, Clone)]
pub struct CacheStats {
    hits: u64,
    misses: u64,
}

impl CacheStats {
    #[inline]
    pub fn hits(&self) -> u64 {
        self.hits
    }

    #[inline]
    pub fn misses(&self) -> u64 {
        self.misses
    }

    #[inline]
    pub fn total(&self) -> u64 {
        self.hits + self.misses
    }

    #[inline]
    pub fn hit_ratio(&self) -> f64 {
        self.hits as f64 / (self.hits + self.misses).max(1) as f64
    }
}

/// Cache with eviction policy that minimizes duplication of keys and values.
#[derive(Debug, Default)]
pub struct Cache<K, V>
where
    K: Clone + Ord + ByteSize,
    V: Clone + ByteSize,
{
    cache: BTreeMap<K, V>,
    capacity: usize,
    size: usize,
    size_limit: usize,
    counter: Counter,
    lru_order: BTreeMap<Counter, K>,
    usage: BTreeMap<K, Counter>,
    stats: CacheStats,
}

impl<K, V> Cache<K, V>
where
    K: Clone + Ord + ByteSize,
    V: Clone + ByteSize,
{
    /// Creates a new cache with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: BTreeMap::new(),
            capacity,
            size: 0,
            size_limit: DEFAULT_SIZE_LIMIT,
            counter: Counter(0),
            lru_order: BTreeMap::new(),
            usage: BTreeMap::new(),
            stats: CacheStats::default(),
        }
    }

    /// Clears the cache.
    pub fn clear(&mut self) {
        self.cache.clear();
        self.lru_order.clear();
        self.usage.clear();
        self.size = 0;
        self.counter = Counter(0);
        self.stats = CacheStats::default();
    }

    /// Retrieves the value associated with the given key and updates the LRU order.
    pub fn get(&mut self, key: &K) -> Option<V> {
        if self.capacity() == 0 && self.size_limit() == 0 {
            return None;
        }
        if let Some(value) = self.cache.get(key).cloned() {
            self.touch(key.clone());
            self.stats.hits += 1;
            return Some(value);
        }
        self.stats.misses += 1;
        None
    }

    /// Inserts the given key and value; if the cache is full, evicts the least-recently used entry.
    pub fn insert(&mut self, key: K, value: V) {
        let capacity = self.capacity();
        if capacity == 0 && self.size_limit() == 0 {
            return;
        }
        while self.len() >= capacity || self.size() > self.size_limit() {
            self.evict_one();
        }
        self.size = self
            .size
            .saturating_add(key.byte_size() + value.byte_size());
        self.cache.insert(key.clone(), value);
        self.touch(key);
    }

    /// Removes the entry associated with the given key.
    pub fn remove(&mut self, key: &K) {
        if self.capacity() == 0 && self.size_limit() == 0 {
            return;
        }
        self.cache.remove(key).inspect(|v| {
            self.size = self.size.saturating_add(v.byte_size());
        });
        if let Some(old_counter) = self.usage.remove(key) {
            self.lru_order.remove(&old_counter).inspect(|k| {
                self.size = self.size.saturating_add(k.byte_size());
            });
        }
    }

    /// Returns the current number of entries in the cache.
    #[inline]
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Returns the cache's size in bytes.
    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the cache's size limit in bytes.
    #[inline]
    pub fn size_limit(&self) -> usize {
        self.size_limit
    }

    /// Sets a new size limit for the cache, evicting entries if necessary.
    pub fn set_size_limit(&mut self, size_limit: usize) {
        self.size_limit = size_limit;
        if size_limit == 0 {
            self.clear();
        } else {
            while self.size() > size_limit {
                self.evict_one();
            }
        }
    }

    /// Returns the cache's capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Sets a new capacity for the cache, evicting entries if necessary.
    pub fn set_capacity(&mut self, capacity: usize) {
        self.capacity = capacity;
        if self.capacity == 0 {
            self.clear();
        } else {
            while self.len() > self.capacity {
                self.evict_one();
            }
        }
    }

    /// Evicts a single entry based on the LRU policy.
    fn evict_one(&mut self) -> bool {
        if let Some((&old_counter, old_key)) = self.lru_order.iter().next() {
            let old_key = old_key.clone();
            self.lru_order.remove(&old_counter).inspect(|k| {
                self.size = self.size.saturating_sub(k.byte_size());
            });
            self.cache.remove(&old_key).inspect(|v| {
                self.size = self.size.saturating_sub(v.byte_size());
            });
            self.usage.remove(&old_key);
            return true;
        }
        false
    }

    /// Updates the LRU order by assigning a new counter for the given id.
    fn touch(&mut self, key: K) {
        let new_counter = {
            let mut counter = self.counter;
            counter.0 += 1;
            counter
        };
        if let Some(old_counter) = self.usage.insert(key.clone(), new_counter) {
            self.lru_order.remove(&old_counter);
        }
        self.lru_order.insert(new_counter, key);
    }

    /// Returns the current cache statistics.
    pub fn stats(&self) -> CacheStats {
        self.stats
    }

    /// Resets the cache statistics.
    pub fn reset_stats(&mut self) {
        self.stats = CacheStats::default();
    }
}
