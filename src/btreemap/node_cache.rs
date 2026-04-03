use crate::types::{Address, NULL};
use crate::Storable;

use super::node::Node;

/// Node-cache performance metrics.
///
/// Counters accumulate over the lifetime of the cache and are **never
/// cleared automatically**. To measure a specific workload, call
/// [`BTreeMap::node_cache_clear_metrics`](super::BTreeMap::node_cache_clear_metrics)
/// before the workload, then read the metrics afterward.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct NodeCacheMetrics {
    /// Successful cache lookups.
    hit_counter: u64,

    /// Misses where the target slot was empty.
    cold_miss_counter: u64,

    /// Misses where the slot was occupied by a different node.
    collision_miss_counter: u64,
}

impl NodeCacheMetrics {
    pub fn new() -> Self {
        Self::default()
    }

    /// Resets all counters to zero.
    pub fn clear_counters(&mut self) {
        self.hit_counter = 0;
        self.cold_miss_counter = 0;
        self.collision_miss_counter = 0;
    }

    /// Returns the number of successful cache lookups.
    pub fn hits(&self) -> u64 {
        self.hit_counter
    }

    /// Returns the number of cache misses where the target slot was empty.
    pub fn cold_misses(&self) -> u64 {
        self.cold_miss_counter
    }

    /// Returns the number of cache misses where the slot was occupied by a different node.
    pub fn collision_misses(&self) -> u64 {
        self.collision_miss_counter
    }

    /// Returns the total number of cache misses.
    pub fn misses(&self) -> u64 {
        self.cold_miss_counter + self.collision_miss_counter
    }

    /// Returns the total number of cache lookups (hits + misses).
    pub fn total(&self) -> u64 {
        self.hit_counter + self.cold_miss_counter + self.collision_miss_counter
    }

    /// Returns the hit ratio as a value between 0.0 and 1.0.
    /// Returns 0.0 if no lookups have been performed.
    pub fn hit_ratio(&self) -> f64 {
        let total = self.total();
        if total == 0 {
            0.0
        } else {
            self.hit_counter as f64 / total as f64
        }
    }

    fn observe_hit(&mut self) {
        self.hit_counter += 1;
    }

    fn observe_cold_miss(&mut self) {
        self.cold_miss_counter += 1;
    }

    fn observe_collision_miss(&mut self) {
        self.collision_miss_counter += 1;
    }
}

/// A single slot in the direct-mapped node cache.
struct CacheSlot<K: Storable + Ord + Clone> {
    /// The stable-memory address of the cached node.
    address: Address,

    /// The cached node, or `None` if the slot is empty.
    node: Option<Node<K>>,

    /// Distance from the tree root (root = 0). Used by the eviction policy.
    depth: u8,
}

impl<K: Storable + Ord + Clone> CacheSlot<K> {
    fn empty() -> Self {
        Self {
            address: NULL,
            node: None,
            depth: 0,
        }
    }
}

/// A direct-mapped node cache.
///
/// Each slot is indexed by `(node_address / page_size) % num_slots`.
/// Collision = eviction (no LRU tracking needed).
///
/// Nodes at depth 0–1 (root and its immediate children) are pinned:
/// they can evict any node but cannot be evicted by deeper nodes.
/// All other nodes compete on pure recency (last writer wins), so
/// hot leaves and working-set interior nodes can displace stale ones.
pub(super) struct NodeCache<K: Storable + Ord + Clone> {
    slots: Vec<CacheSlot<K>>,
    page_size: u32,
    metrics: NodeCacheMetrics,
}

impl<K: Storable + Ord + Clone> NodeCache<K> {
    pub(super) fn new(page_size: u32, num_slots: usize) -> Self {
        let mut slots = Vec::with_capacity(num_slots);
        for _ in 0..num_slots {
            slots.push(CacheSlot::empty());
        }
        Self {
            slots,
            page_size,
            metrics: NodeCacheMetrics::new(),
        }
    }

    pub(super) fn is_enabled(&self) -> bool {
        !self.slots.is_empty()
    }

    pub(super) fn num_slots(&self) -> usize {
        self.slots.len()
    }

    pub(super) fn clear(&mut self) {
        for slot in &mut self.slots {
            *slot = CacheSlot::empty();
        }
        self.metrics.clear_counters();
    }

    pub(super) fn slot_size() -> usize {
        std::mem::size_of::<CacheSlot<K>>()
    }

    fn slot_index(&self, addr: Address) -> usize {
        debug_assert!(self.is_enabled());
        (addr.get() / self.page_size as u64) as usize % self.slots.len()
    }

    pub(super) fn take(&mut self, addr: Address) -> Option<Node<K>> {
        if !self.is_enabled() || addr == NULL {
            return None;
        }
        let idx = self.slot_index(addr);
        let slot = &mut self.slots[idx];
        if slot.address == addr {
            self.metrics.observe_hit();
            slot.address = NULL;
            slot.node.take()
        } else {
            if slot.node.is_none() {
                self.metrics.observe_cold_miss();
            } else {
                self.metrics.observe_collision_miss();
            }
            None
        }
    }

    pub(super) fn put(&mut self, addr: Address, node: Node<K>, depth: u8) {
        if !self.is_enabled() {
            return;
        }
        let idx = self.slot_index(addr);
        let slot = &mut self.slots[idx];
        // Always cache into empty slots. Depth 0–1 (root + its children)
        // are pinned: a shallower-or-equal pinned node always wins its
        // slot, and no unpinned node can displace a pinned one. Among
        // unpinned nodes (depth 2+), pure recency applies: any unpinned
        // node can evict any other unpinned node, letting hot leaves
        // displace stale interior nodes.
        let dominated = depth <= slot.depth;
        let both_unpinned = depth > 1 && slot.depth > 1;
        if slot.node.is_none() || dominated || both_unpinned {
            *slot = CacheSlot {
                address: addr,
                node: Some(node),
                depth,
            };
        }
    }

    pub(super) fn invalidate(&mut self, addr: Address) {
        if !self.is_enabled() {
            return;
        }
        let idx = self.slot_index(addr);
        let slot = &mut self.slots[idx];
        if slot.address == addr {
            *slot = CacheSlot::empty();
        }
    }

    pub(super) fn metrics(&self) -> NodeCacheMetrics {
        self.metrics
    }

    pub(super) fn clear_metrics(&mut self) {
        self.metrics.clear_counters();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::btreemap::node::{NodeType, PageSize};

    const PAGE_SIZE: u32 = 64;
    const NUM_SLOTS: usize = 4;

    fn make_cache() -> NodeCache<Vec<u8>> {
        NodeCache::new(PAGE_SIZE, NUM_SLOTS)
    }

    /// Creates a leaf node at the given address.
    fn leaf(addr: u64) -> Node<Vec<u8>> {
        Node::new_v2(Address::from(addr), NodeType::Leaf, PageSize::Value(512))
    }

    /// First realistic node address (past allocator header + chunk header).
    const ADDR_A: u64 = 116;
    /// Second address that maps to the same cache slot as ADDR_A.
    const ADDR_B: u64 = ADDR_A + NUM_SLOTS as u64 * PAGE_SIZE as u64;

    /// Returns a pair of non-NULL addresses that map to the same cache slot.
    fn colliding_pair() -> (Address, Address) {
        (Address::from(ADDR_A), Address::from(ADDR_B))
    }

    #[test]
    fn put_and_take() {
        let mut cache = make_cache();
        let addr = Address::from(ADDR_A);
        cache.put(addr, leaf(ADDR_A), 0);
        assert!(cache.take(addr).is_some());
    }

    #[test]
    fn take_removes_entry() {
        let mut cache = make_cache();
        let addr = Address::from(ADDR_A);
        cache.put(addr, leaf(ADDR_A), 0);
        cache.take(addr);
        assert!(cache.take(addr).is_none());
    }

    #[test]
    fn take_miss_on_empty_slot() {
        let mut cache = make_cache();
        assert!(cache.take(Address::from(ADDR_A)).is_none());
    }

    #[test]
    fn take_miss_on_wrong_address() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 2);
        assert!(cache.take(b).is_none());
    }

    #[test]
    fn invalidate_removes_entry() {
        let mut cache = make_cache();
        let addr = Address::from(ADDR_A);
        cache.put(addr, leaf(ADDR_A), 0);
        cache.invalidate(addr);
        assert!(cache.take(addr).is_none());
    }

    #[test]
    fn invalidate_ignores_wrong_address() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 2);
        cache.invalidate(b); // different address, same slot
        assert!(cache.take(a).is_some());
    }

    #[test]
    fn depth0_cannot_be_evicted_by_depth1() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 0);
        cache.put(b, leaf(ADDR_B), 1);
        // depth-0 node survives
        assert!(cache.take(a).is_some());
    }

    #[test]
    fn depth0_cannot_be_evicted_by_depth2() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 0);
        cache.put(b, leaf(ADDR_B), 2);
        assert!(cache.take(a).is_some());
    }

    #[test]
    fn depth1_cannot_be_evicted_by_depth2() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 1);
        cache.put(b, leaf(ADDR_B), 2);
        assert!(cache.take(a).is_some());
    }

    #[test]
    fn depth0_evicts_depth1() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 1);
        cache.put(b, leaf(ADDR_B), 0);
        // depth-0 replaced depth-1
        assert!(cache.take(b).is_some());
        assert!(cache.take(a).is_none());
    }

    #[test]
    fn depth0_evicts_depth2() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 2);
        cache.put(b, leaf(ADDR_B), 0);
        assert!(cache.take(b).is_some());
    }

    #[test]
    fn depth1_evicts_depth2() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 2);
        cache.put(b, leaf(ADDR_B), 1);
        assert!(cache.take(b).is_some());
    }

    // ---------------------------------------------------------------
    // Eviction policy: unpinned levels (depth 2+) compete on recency
    // ---------------------------------------------------------------

    #[test]
    fn depth3_evicts_depth2() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 2);
        cache.put(b, leaf(ADDR_B), 3);
        // recency wins — deeper node replaced shallower
        assert!(cache.take(b).is_some());
        assert!(cache.take(a).is_none());
    }

    #[test]
    fn depth2_evicts_depth5() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 5);
        cache.put(b, leaf(ADDR_B), 2);
        assert!(cache.take(b).is_some());
    }

    #[test]
    fn same_depth_evicts() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 3);
        cache.put(b, leaf(ADDR_B), 3);
        assert!(cache.take(b).is_some());
        assert!(cache.take(a).is_none());
    }

    // ---------------------------------------------------------------
    // Disabled cache
    // ---------------------------------------------------------------

    #[test]
    fn disabled_cache_returns_none() {
        let mut cache: NodeCache<Vec<u8>> = NodeCache::new(PAGE_SIZE, 0);
        assert!(!cache.is_enabled());
        cache.put(Address::from(ADDR_A), leaf(ADDR_A), 0);
        assert!(cache.take(Address::from(ADDR_A)).is_none());
    }

    // ---------------------------------------------------------------
    // NULL address
    // ---------------------------------------------------------------

    #[test]
    fn take_null_returns_none() {
        let mut cache = make_cache();
        assert!(cache.take(NULL).is_none());
    }

    // ---------------------------------------------------------------
    // Metrics
    // ---------------------------------------------------------------

    #[test]
    fn metrics_hit() {
        let mut cache = make_cache();
        let addr = Address::from(ADDR_A);
        cache.put(addr, leaf(ADDR_A), 0);
        cache.take(addr);
        assert_eq!(cache.metrics().hits(), 1);
    }

    #[test]
    fn metrics_cold_miss() {
        let mut cache = make_cache();
        cache.take(Address::from(ADDR_A));
        assert_eq!(cache.metrics().cold_misses(), 1);
        assert_eq!(cache.metrics().collision_misses(), 0);
    }

    #[test]
    fn metrics_collision_miss() {
        let mut cache = make_cache();
        let (a, b) = colliding_pair();
        cache.put(a, leaf(ADDR_A), 2);
        cache.clear_metrics();
        cache.take(b); // occupied by a, not b
        assert_eq!(cache.metrics().collision_misses(), 1);
        assert_eq!(cache.metrics().cold_misses(), 0);
    }

    #[test]
    fn clear_resets_slots_and_metrics() {
        let mut cache = make_cache();
        let addr = Address::from(ADDR_A);
        cache.put(addr, leaf(ADDR_A), 0);
        cache.take(addr);
        cache.clear();
        assert_eq!(cache.metrics().total(), 0);
        assert!(cache.take(addr).is_none());
    }
}
