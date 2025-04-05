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
        if self.capacity() == 0 || self.size_limit() == 0 {
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

    /// Inserts the given key and value; if the cache is full or exceeds the size limit, evicts the least-recently used entry.
    pub fn insert(&mut self, key: K, value: V) {
        if self.capacity() == 0 || self.size_limit() == 0 {
            return;
        }
        let delta = key.byte_size() + value.byte_size();
        while self.len() + 1 > self.capacity() || self.size() + delta > self.size_limit() {
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
        if self.capacity() == 0 || self.size_limit() == 0 {
            return;
        }
        if let Some(v) = self.cache.remove(key) {
            self.size = self.size.saturating_sub(key.byte_size() + v.byte_size());
        }
        if let Some(old_counter) = self.usage.remove(key) {
            if let Some(removed_key) = self.lru_order.remove(&old_counter) {
                self.size = self.size.saturating_sub(removed_key.byte_size());
            }
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
    fn evict_one(&mut self) -> Option<K> {
        if let Some((&old_counter, old_key)) = self.lru_order.iter().next() {
            let old_key = old_key.clone();
            if let Some(k) = self.lru_order.remove(&old_counter) {
                self.size = self.size.saturating_sub(k.byte_size());
            }
            if let Some(v) = self.cache.remove(&old_key) {
                self.size = self
                    .size
                    .saturating_sub(old_key.byte_size() + v.byte_size());
            }
            self.usage.remove(&old_key);
            return Some(old_key);
        }
        None
    }

    /// Updates the LRU order by assigning a new counter for the given key.
    fn touch(&mut self, key: K) {
        self.counter.0 += 1;
        let new_counter = self.counter;
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

#[cfg(test)]
mod tests {
    use super::*;

    impl ByteSize for u32 {
        fn byte_size(&self) -> usize {
            std::mem::size_of_val(self)
        }
    }

    #[test]
    fn test_insert_and_get() {
        let mut cache: Cache<u32, u32> = Cache::new(5);
        cache.insert(1u32, 100u32);
        cache.insert(2u32, 200u32);

        // Test that values can be retrieved.
        assert_eq!(cache.get(&1), Some(100));
        assert_eq!(cache.get(&2), Some(200));
        // Test stats: two successful gets.
        let stats = cache.stats();
        assert_eq!(stats.hits(), 2);
        assert_eq!(stats.misses(), 0);
    }

    #[test]
    fn test_miss() {
        let mut cache: Cache<u32, u32> = Cache::new(5);
        // Attempt to retrieve a key that was never inserted.
        assert_eq!(cache.get(&1), None);
        let stats = cache.stats();
        assert_eq!(stats.hits(), 0);
        assert_eq!(stats.misses(), 1);
    }

    #[test]
    fn test_eviction_by_capacity() {
        // Create a cache with a capacity of 3 entries.
        let mut cache: Cache<u32, u32> = Cache::new(3);
        cache.insert(1u32, 10u32);
        cache.insert(2u32, 20u32);
        cache.insert(3u32, 30u32);

        // Inserting a fourth entry should evict one entry (the LRU).
        cache.insert(4u32, 40u32);

        // With LRU eviction, the least recently used key (1) should be gone.
        assert_eq!(cache.get(&1), None);
        // The other keys should be available.
        assert_eq!(cache.get(&2), Some(20));
        assert_eq!(cache.get(&3), Some(30));
        assert_eq!(cache.get(&4), Some(40));
    }

    #[test]
    fn test_eviction_by_size_limit() {
        // Use a cache with a generous capacity but a small size limit.
        let mut cache: Cache<u32, u32> = Cache::new(10);
        // Set a size limit small enough so that only two u32 entries (approx 8 bytes each)
        // can be kept before eviction kicks in.
        cache.set_size_limit(16);
        cache.insert(1u32, 10u32); // approx 8 bytes (key + value)
        cache.insert(2u32, 20u32); // approx 8 bytes more, total around 16 bytes

        // Inserting another entry should trigger eviction due to size limit.
        cache.insert(3u32, 30u32);

        // Expect that one entry is evicted. Assuming LRU policy, key 1 is evicted.
        assert_eq!(cache.get(&1), None);
        // The remaining entries should be present.
        assert_eq!(cache.get(&2), Some(20));
        assert_eq!(cache.get(&3), Some(30));
    }

    #[test]
    fn test_remove() {
        let mut cache: Cache<u32, u32> = Cache::new(5);
        cache.insert(1u32, 10u32);
        cache.insert(2u32, 20u32);

        // Remove key 1.
        cache.remove(&1);
        assert_eq!(cache.get(&1), None);
        // Removing a non-existing key should not cause issues.
        cache.remove(&3);
        // Key 2 should still be retrievable.
        assert_eq!(cache.get(&2), Some(20));
    }

    #[test]
    fn test_clear() {
        let mut cache: Cache<u32, u32> = Cache::new(5);
        cache.insert(1u32, 10u32);
        cache.insert(2u32, 20u32);
        cache.insert(3u32, 30u32);

        cache.clear();
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2), None);
        assert_eq!(cache.get(&3), None);
    }

    #[test]
    fn test_stats() {
        let mut cache: Cache<u32, u32> = Cache::new(3);
        // Initially, no hits or misses.
        let stats = cache.stats();
        assert_eq!(stats.hits(), 0);
        assert_eq!(stats.misses(), 0);

        // Inserting and accessing some keys.
        cache.insert(1u32, 10u32);
        cache.insert(2u32, 20u32);

        // A hit.
        let _ = cache.get(&1);
        // A miss.
        let _ = cache.get(&3);

        let stats = cache.stats();
        assert_eq!(stats.hits(), 1);
        assert_eq!(stats.misses(), 1);
    }
}
