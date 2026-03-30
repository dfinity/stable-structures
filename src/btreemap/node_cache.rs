use crate::types::{Address, NULL};
use crate::Storable;

use super::node::Node;

/// Node-cache performance metrics.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct NodeCacheMetrics {
    hits_counter: u64,
    misses_counter: u64,
}

impl NodeCacheMetrics {
    pub fn new() -> Self {
        Self::default()
    }

    /// Resets all counters to zero.
    pub fn clear_counters(&mut self) {
        self.hits_counter = 0;
        self.misses_counter = 0;
    }

    pub fn hits(&self) -> u64 {
        self.hits_counter
    }

    pub fn misses(&self) -> u64 {
        self.misses_counter
    }

    pub fn total(&self) -> u64 {
        self.hits_counter + self.misses_counter
    }

    /// Returns the hit ratio as a value between 0.0 and 1.0.
    /// Returns 0.0 if no lookups have been performed.
    pub fn hit_ratio(&self) -> f64 {
        let total = self.total();
        if total == 0 {
            0.0
        } else {
            self.hits_counter as f64 / total as f64
        }
    }

    fn observe_hit(&mut self) {
        self.hits_counter += 1;
    }

    fn observe_miss(&mut self) {
        self.misses_counter += 1;
    }
}

/// A single slot in the direct-mapped node cache.
struct CacheSlot<K: Storable + Ord + Clone> {
    /// The stable-memory address of the cached node.
    address: Address,
    /// The cached node, or `None` if the slot is empty.
    node: Option<Node<K>>,
    /// Distance from the tree root (root = 0). Used to resolve
    /// collisions: shallower nodes are kept over deeper ones.
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
/// Upper tree levels (root, depth-1) naturally stay cached because their
/// addresses are stable and map to distinct slots. The depth-aware
/// eviction policy further guarantees that a deeper node can never
/// displace a shallower one from a shared slot.
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

    fn slot_index(&self, addr: Address) -> usize {
        debug_assert!(self.is_enabled());
        (addr.get() / self.page_size as u64) as usize % self.slots.len()
    }

    pub(super) fn take(&mut self, addr: Address) -> Option<Node<K>> {
        debug_assert!(self.is_enabled());
        let idx = self.slot_index(addr);
        let slot = &mut self.slots[idx];
        if slot.address == addr {
            self.metrics.observe_hit();
            slot.address = NULL;
            slot.node.take()
        } else {
            self.metrics.observe_miss();
            None
        }
    }

    pub(super) fn put(&mut self, addr: Address, node: Node<K>, depth: u8) {
        debug_assert!(self.is_enabled());
        let idx = self.slot_index(addr);
        let slot = &mut self.slots[idx];
        // Only evict an existing cached node if the new node is at the
        // same depth or closer to the root (lower depth value).
        // This keeps upper-level nodes cached even when a deeper node
        // maps to the same slot.
        if slot.node.is_none() || depth <= slot.depth {
            *slot = CacheSlot {
                address: addr,
                node: Some(node),
                depth,
            };
        }
    }

    pub(super) fn invalidate(&mut self, addr: Address) {
        debug_assert!(self.is_enabled());
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

    pub(super) fn clear(&mut self) {
        for slot in &mut self.slots {
            *slot = CacheSlot::empty();
        }
        self.metrics.clear_counters();
    }

    pub(super) fn slot_size() -> usize {
        std::mem::size_of::<CacheSlot<K>>()
    }
}
