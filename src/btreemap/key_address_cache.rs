use crate::types::Address;
use std::collections::BTreeMap;

#[allow(non_upper_case_globals)]
const KiB: usize = 1024;
#[allow(non_upper_case_globals)]
const MiB: usize = 1024 * KiB;
#[allow(non_upper_case_globals)]
const GiB: usize = 1024 * MiB;

const DEFAULT_CAPACITY: usize = 0;

/// Incrementing counter used for tracking the order of usage.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Default)]
struct Counter(u64);

/// Cache with eviction policy that minimizes duplication of keys and values.
#[derive(Debug, Default, Clone)]
pub struct KeyAddressCache<K>
where
    K: Clone + Ord,
{
    key_to_address: BTreeMap<K, Address>,
    address_to_keys: BTreeMap<Address, Vec<K>>,
    capacity: usize,
    counter: Counter,
    lru_order: BTreeMap<Counter, K>,
    usage: BTreeMap<K, Counter>,
    stats: CacheStats,
}

impl<K> KeyAddressCache<K>
where
    K: Clone + Ord,
{
    /// Creates a new cache with the given capacity.
    pub fn new() -> Self {
        Self {
            key_to_address: BTreeMap::new(),
            address_to_keys: BTreeMap::new(),
            capacity: DEFAULT_CAPACITY,
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

    /// Clears all entries and resets statistics.
    pub fn clear(&mut self) {
        self.key_to_address.clear();
        self.address_to_keys.clear();
        self.counter = Counter(0);
        self.lru_order.clear();
        self.usage.clear();
        self.stats = CacheStats::default();
    }

    /// Retrieves the address for the given key (if any) and updates its LRU status.
    pub fn get(&mut self, key: &K) -> Option<Address> {
        if self.capacity == 0 {
            return None;
        }
        if let Some(address) = self.key_to_address.get(key).cloned() {
            self.touch(key.clone());
            self.stats.hits += 1;
            return Some(address);
        }
        self.stats.misses += 1;
        None
    }

    /// Inserts the given key and address.
    /// If adding this entry would exceed the capacity or size limit, evicts LRU entries.
    pub fn insert(&mut self, key: K, address: Address) {
        if self.capacity == 0 {
            return;
        }
        while self.len() + 1 > self.capacity {
            self.evict_one();
        }
        self.key_to_address.insert(key.clone(), address);
        self.address_to_keys
            .entry(address)
            .or_default()
            .push(key.clone());
        self.touch(key);
    }

    /// Removes the entry associated with the given key.
    pub fn remove(&mut self, key: &K) {
        if self.capacity == 0 {
            return;
        }
        if let Some(address) = self.key_to_address.remove(key) {
            if let Some(keys) = self.address_to_keys.get_mut(&address) {
                keys.retain(|k| k != key);
                if keys.is_empty() {
                    self.address_to_keys.remove(&address);
                }
            }
        }
        if let Some(counter) = self.usage.remove(key) {
            self.lru_order.remove(&counter);
        }
    }

    /// Removes all entries associated with the given address.
    pub fn remove_address(&mut self, address: &Address) {
        if self.capacity == 0 {
            return;
        }
        if let Some(keys) = self.address_to_keys.remove(address) {
            for key in keys {
                self.key_to_address.remove(&key);
                if let Some(counter) = self.usage.remove(&key) {
                    self.lru_order.remove(&counter);
                }
            }
        }
    }

    /// Returns the number of entries in the cache.
    #[inline]
    pub fn len(&self) -> usize {
        self.key_to_address.len()
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
            self.key_to_address.remove(&old_key);
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

impl<K> Drop for KeyAddressCache<K>
where
    K: Clone + Ord,
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

    fn user(id: u8) -> Principal {
        Principal::from_slice(&[id])
    }

    fn addr(id: u64) -> Address {
        Address::from(id)
    }

    #[test]
    fn test_insert_and_get() {
        let mut cache = KeyAddressCache::new().with_capacity(5);
        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(200));

        // Test that addresses can be retrieved.
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
    fn test_remove_address() {
        let mut cache = KeyAddressCache::new().with_capacity(5);
        cache.insert(user(1), addr(100));
        cache.insert(user(2), addr(100));
        cache.insert(user(3), addr(200));

        cache.remove_address(&addr(100));
        assert_eq!(cache.get(&user(1)), None);
        assert_eq!(cache.get(&user(2)), None);
        assert_eq!(cache.get(&user(3)), Some(addr(200)));
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
