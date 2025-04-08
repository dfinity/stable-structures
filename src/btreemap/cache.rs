use std::collections::BTreeMap;

#[allow(non_upper_case_globals)]
const KiB: usize = 1024;
#[allow(non_upper_case_globals)]
const MiB: usize = 1024 * KiB;
#[allow(non_upper_case_globals)]
const GiB: usize = 1024 * MiB;

const DEFAULT_CAPACITY: usize = 0;
const DEFAULT_SIZE_LIMIT: usize = 3 * GiB;

pub trait ByteSize {
    /// Returns the size (in bytes) of the value.
    fn byte_size(&self) -> usize {
        std::mem::size_of_val(self)
    }
}

/// Incrementing counter used for tracking the order of usage.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Default)]
struct Counter(u64);

/// Cache with eviction policy that minimizes duplication of keys and values.
#[derive(Debug, Default, Clone)]
pub struct Cache<K, V>
where
    K: Clone + Ord + ByteSize,
    V: Clone + ByteSize,
{
    key_to_value: BTreeMap<K, V>,
    capacity: usize,
    /// Tracks the cumulative bytes for all entries (including duplicated key storage).
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
    /// Computes the total overhead of an entry:
    /// - 3 * key_size (key_to_value, lru_order, usage)
    /// - value_size (key_to_value)
    /// - 2 * size_of(Counter) (for the LRU order and usage tracking)
    fn entry_overhead(key_size: usize, value_size: usize) -> usize {
        3 * key_size + value_size + 2 * std::mem::size_of::<Counter>()
    }

    /// Creates a new cache with the given capacity.
    pub fn new() -> Self {
        Self {
            key_to_value: BTreeMap::new(),
            capacity: DEFAULT_CAPACITY,
            size: 0,
            size_limit: DEFAULT_SIZE_LIMIT,
            counter: Counter(0),
            lru_order: BTreeMap::new(),
            usage: BTreeMap::new(),
            stats: CacheStats::default(),
        }
    }

    /// Creates a new cache with the given capacity and size limit.
    pub fn with_capacity(self, capacity: usize) -> Self {
        let mut this = self.clone();
        this.capacity = capacity;
        this
    }

    /// Creates a new cache with the given size limit.
    pub fn with_size_limit(self, size_limit: usize) -> Self {
        let mut this = self.clone();
        this.size_limit = size_limit;
        this
    }

    /// Clears all entries and resets statistics.
    pub fn clear(&mut self) {
        self.key_to_value.clear();
        self.size = 0;
        self.counter = Counter(0);
        self.lru_order.clear();
        self.usage.clear();
        self.stats = CacheStats::default();
    }

    /// Retrieves the value for the given key (if any) and updates its LRU status.
    pub fn get(&mut self, key: &K) -> Option<V> {
        if self.capacity == 0 || self.size_limit == 0 {
            return None;
        }
        if let Some(value) = self.key_to_value.get(key).cloned() {
            self.touch(key.clone());
            self.stats.hits += 1;
            return Some(value);
        }
        self.stats.misses += 1;
        None
    }

    /// Inserts the given key and value.
    /// If adding this entry would exceed the capacity or size limit, evicts LRU entries.
    pub fn insert(&mut self, key: K, value: V) {
        if self.capacity == 0 || self.size_limit == 0 {
            return;
        }
        let (key_size, value_size) = (key.byte_size(), value.byte_size());
        let overhead = Self::entry_overhead(key_size, value_size);
        while self.len() + 1 > self.capacity() || self.size + overhead > self.size_limit() {
            self.evict_one();
        }
        if self.key_to_value.insert(key.clone(), value).is_none() {
            self.size = self.size.saturating_add(key_size + value_size);
        }
        self.touch(key);
    }

    /// Removes the entry associated with the given key.
    pub fn remove(&mut self, key: &K) {
        if self.capacity == 0 || self.size_limit == 0 {
            return;
        }
        if let Some(value) = self.key_to_value.remove(key) {
            let (key_size, value_size) = (key.byte_size(), value.byte_size());
            let overhead = Self::entry_overhead(key_size, value_size);
            self.size = self.size.saturating_sub(overhead);
        }
        if let Some(counter) = self.usage.remove(key) {
            self.lru_order.remove(&counter);
        }
    }

    /// Returns the number of entries in the cache.
    #[inline]
    pub fn len(&self) -> usize {
        self.key_to_value.len()
    }

    /// Returns the total size in bytes of all entries (including duplicate key storage).
    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the configured size limit (in bytes).
    #[inline]
    pub fn size_limit(&self) -> usize {
        self.size_limit
    }

    /// Sets a new size limit, evicting entries as necessary.
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

    /// Returns the cache capacity (number of entries).
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Sets a new capacity, evicting entries as needed.
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

    /// Evicts a single entry using the LRU policy.
    /// Returns the key that was evicted.
    fn evict_one(&mut self) -> Option<K> {
        // Find the least-recently used entry.
        if let Some((&old_counter, old_key)) = self.lru_order.iter().next() {
            let old_key = old_key.clone();
            let key_size = old_key.byte_size();
            let overhead = Self::entry_overhead(key_size, 0);
            self.size = self.size.saturating_sub(overhead);
            if let Some(v) = self.key_to_value.remove(&old_key) {
                self.size = self.size.saturating_sub(v.byte_size());
            }
            self.lru_order.remove(&old_counter);
            self.usage.remove(&old_key);
            return Some(old_key);
        }
        None
    }

    /// Updates the LRU order for the given key.
    /// If the key is already in the LRU maps, its old counter is replaced.
    /// For a new key, the overhead for the key (in usage and lru_order) is added.
    fn touch(&mut self, key: K) {
        self.counter.0 += 1;
        let new_counter = self.counter;
        let delta: usize = key.byte_size() + std::mem::size_of::<Counter>();
        // Update usage: if key was present, remove its old LRU overhead.
        if let Some(old_counter) = self.usage.insert(key.clone(), new_counter) {
            if self.lru_order.remove(&old_counter).is_some() {
                self.size = self.size.saturating_sub(delta);
            }
        } else {
            // New key in usage.
            self.size = self.size.saturating_add(delta);
        }
        // Insert into lru_order. If newly inserted, add the overhead.
        if self.lru_order.insert(new_counter, key).is_none() {
            self.size = self.size.saturating_add(delta);
        }
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

impl<K, V> Drop for Cache<K, V>
where
    K: Clone + Ord + ByteSize,
    V: Clone + ByteSize,
{
    fn drop(&mut self) {
        // crate::debug::print(&format!("ABC cache len       : {}", self.len()));
        // crate::debug::print(&format!("ABC cache size      : {}", self.size()));
        // crate::debug::print(&format!(
        //     "ABC cache hit ratio : {:>.1} %",
        //     self.stats().hit_ratio() * 100.0
        // ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Address;
    use ic_principal::Principal;
    use std::mem::size_of;

    impl ByteSize for Principal {
        fn byte_size(&self) -> usize {
            self.as_slice().len()
        }
    }
    impl ByteSize for Address {}

    type KeyAddressCache = Cache<Principal, Address>;

    fn user(id: u8) -> Principal {
        Principal::from_slice(&[id])
    }

    fn addr(id: u64) -> Address {
        Address::from(id)
    }

    /// Helper: returns the expected overhead (in bytes) for an entry with key type u32 and value type u64.
    /// Calculation: 3 * size_of(u32) + size_of(u64)
    fn entry_size() -> usize {
        let key_size = Principal::anonymous().byte_size();
        let value_size = Address::from(0).byte_size();
        3 * key_size + value_size + 2 * size_of::<Counter>()
    }

    #[test]
    fn test_insert_and_get() {
        let mut cache = KeyAddressCache::new().with_capacity(5);
        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(200));

        // Test that values can be retrieved.
        assert_eq!(cache.get(&user(1)), Some(addr(100)));
        assert_eq!(cache.get(&user(2)), Some(addr(200)));

        // Test stats: two successful gets.
        let stats = cache.stats();
        assert_eq!(stats.hits(), 2);
        assert_eq!(stats.misses(), 0);
    }

    #[test]
    fn test_miss() {
        let mut cache = KeyAddressCache::new().with_capacity(5);
        // Attempt to retrieve a key that was never inserted.
        assert_eq!(cache.get(&user(1)), None);

        let stats = cache.stats();
        assert_eq!(stats.hits(), 0);
        assert_eq!(stats.misses(), 1);
    }

    #[test]
    fn test_cache_size_tracking() {
        // Allow at most two entries.
        let mut cache = KeyAddressCache::new()
            .with_capacity(5)
            .with_size_limit(2 * entry_size());

        // Insert first entry.
        cache.insert(user(1), addr(100));
        assert_eq!(cache.size(), entry_size());
        assert_eq!(cache.get(&user(1)), Some(addr(100)));

        // Insert the same entry again should not change the overall size.
        cache.insert(user(1), addr(100));
        assert_eq!(cache.size(), entry_size());
        assert_eq!(cache.get(&user(1)), Some(addr(100)));

        // Insert second entry.
        cache.insert(user(2), addr(200));
        assert_eq!(cache.size(), 2 * entry_size());
        assert_eq!(cache.get(&user(1)), Some(addr(100)));
        assert_eq!(cache.get(&user(2)), Some(addr(200)));

        // Inserting a third entry should trigger eviction (LRU policy) so that the size remains unchanged.
        cache.insert(user(3), addr(300));
        assert_eq!(cache.size(), 2 * entry_size());
        // Expect the least-recently used entry (key 1) to be evicted.
        assert_eq!(cache.get(&user(1)), None);
        assert_eq!(cache.get(&user(2)), Some(addr(200)));
        assert_eq!(cache.get(&user(3)), Some(addr(300)));

        // Remove an entry.
        cache.remove(&user(2));
        assert_eq!(cache.size(), entry_size());
        cache.remove(&user(3));
        assert_eq!(cache.size(), 0);
    }

    #[test]
    fn test_eviction_by_capacity() {
        let mut cache = KeyAddressCache::new().with_capacity(3);
        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(200));
        cache.insert(user(3), addr(300));

        // Inserting a fourth entry should evict the LRU entry.
        cache.insert(user(4), addr(400));

        // Expect key 1 to be evicted.
        assert_eq!(cache.get(&user(1)), None);
        // The other keys should be available.
        assert_eq!(cache.get(&user(2)), Some(addr(200)));
        assert_eq!(cache.get(&user(3)), Some(addr(300)));
        assert_eq!(cache.get(&user(4)), Some(addr(400)));
    }

    #[test]
    fn test_eviction_by_size_limit() {
        // Set a size limit to allow only two entries.
        let mut cache = KeyAddressCache::new()
            .with_capacity(10)
            .with_size_limit(2 * entry_size());

        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(200));

        // Inserting another entry should trigger eviction due to the size limit.
        cache.insert(user(3), addr(300));

        // Expect that one entry is evicted (key 1, as the LRU).
        assert_eq!(cache.get(&user(1)), None);
        assert_eq!(cache.get(&user(2)), Some(addr(200)));
        assert_eq!(cache.get(&user(3)), Some(addr(300)));
    }

    #[test]
    fn test_remove() {
        let mut cache = KeyAddressCache::new().with_capacity(5);
        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(200));

        // Remove key 1.
        cache.remove(&user(1));
        assert_eq!(cache.get(&user(1)), None);
        // Removing a non-existent key should be safe.
        cache.remove(&user(3));
        // Key 2 should still be retrievable.
        assert_eq!(cache.get(&user(2)), Some(addr(200)));
    }

    #[test]
    fn test_clear() {
        let mut cache = KeyAddressCache::new().with_capacity(5);
        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(200));
        cache.insert(user(3), addr(300));

        cache.clear();
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.get(&user(1)), None);
        assert_eq!(cache.get(&user(2)), None);
        assert_eq!(cache.get(&user(3)), None);
    }

    #[test]
    fn test_stats() {
        let mut cache = KeyAddressCache::new().with_capacity(3);
        // Initially, no hits or misses.
        let stats = cache.stats();
        assert_eq!(stats.hits(), 0);
        assert_eq!(stats.misses(), 0);

        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(200));

        // One hit.
        let _ = cache.get(&user(1));
        // One miss.
        let _ = cache.get(&user(3));

        let stats = cache.stats();
        assert_eq!(stats.hits(), 1);
        assert_eq!(stats.misses(), 1);
    }
}
