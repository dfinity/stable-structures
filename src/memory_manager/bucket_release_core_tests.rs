//! Core memory reclamation functionality tests for MemoryManager.
//!
//! These tests verify the basic memory management operations without dependency
//! on specific data structures. They test the fundamental bucket allocation,
//! reclamation, and reuse mechanisms.
//!
//! **CRITICAL SAFETY REQUIREMENTS**:
//! All memory reclamation operations require mandatory Rust object drop BEFORE reclamation.
//! Using original data structures after memory reclamation causes data corruption.
//! See MemoryManager documentation for proper usage patterns.

use super::{MemoryId, MemoryManager};
use crate::{btreemap::BTreeMap, vec_mem::VectorMemory, Memory};

/// Helper to create a minimal data structure for bucket allocation
fn allocate_buckets_via_btreemap(
    mm: &MemoryManager<VectorMemory>,
    memory_id: MemoryId,
    count: u64,
) {
    let mut map = BTreeMap::init(mm.get(memory_id));
    for i in 0..count {
        map.insert(i, vec![42u8; 2000]); // 2KB blob to trigger bucket allocation
    }
    drop(map); // Drop the structure before memory reclamation
}

#[test]
fn reclaim_empty_memory_returns_zero() {
    // Test: Reclaiming memory from unused memory should return 0
    let memory_id = MemoryId::new(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Try to reclaim memory from empty memory
    let pages_reclaimed = mm.reclaim_memory(memory_id);

    // Should return 0 since no pages were allocated
    assert_eq!(pages_reclaimed, 0, "Empty memory should reclaim 0 pages");
}

#[test]
fn double_reclaim_returns_zero_second_time() {
    // Test: Reclaiming the same memory twice should return 0 on second attempt
    let memory_id = MemoryId::new(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Allocate buckets and clear structure
    allocate_buckets_via_btreemap(&mm, memory_id, 50);

    // First release should return non-zero
    let first_release = mm.reclaim_memory(memory_id);
    assert!(first_release > 0, "First reclaim should return pages > 0");

    // Second release should return 0 (nothing left to release)
    let second_release = mm.reclaim_memory(memory_id);
    assert_eq!(second_release, 0, "Second reclaim should return 0 pages");
}

#[test]
fn reclaim_only_affects_target_memory() {
    // Test: Reclaiming memory A should not affect memory B's buckets
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Allocate buckets in both memories
    allocate_buckets_via_btreemap(&mm, a, 30);
    allocate_buckets_via_btreemap(&mm, b, 30);

    // Reclaim A's memory
    let pages_reclaimed = mm.reclaim_memory(a);
    assert!(pages_reclaimed > 0, "Should reclaim A's pages");

    // Verify B still has its memory (can't be reclaimed again)
    let b_reclaim_attempt = mm.reclaim_memory(b);
    assert!(
        b_reclaim_attempt > 0,
        "B should still have reclaimable pages"
    );
}

#[test]
fn multiple_reclaim_cycles() {
    // Test: Multiple allocate→reclaim cycles should work consistently
    let memory_id = MemoryId::new(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Perform several cycles of allocate→reclaim
    for cycle in 0..5 {
        // Allocate buckets
        allocate_buckets_via_btreemap(&mm, memory_id, 40);

        // Reclaim memory
        let pages_reclaimed = mm.reclaim_memory(memory_id);

        assert!(
            pages_reclaimed > 0,
            "Cycle {} should reclaim >0 pages, got {}",
            cycle,
            pages_reclaimed
        );
    }
}

#[test]
fn bucket_reuse_prevents_memory_growth() {
    // Test: Reclaimed buckets are actually reused by subsequent allocations
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate buckets in A
    allocate_buckets_via_btreemap(&mm, a, 50);

    // Reclaim A's memory
    let pages_reclaimed = mm.reclaim_memory(a);
    assert!(pages_reclaimed > 0);
    let stable_before = mock_stable_memory.size();

    // Allocate same amount in B → should reuse A's reclaimed buckets
    allocate_buckets_via_btreemap(&mm, b, 50);
    let stable_after = mock_stable_memory.size();

    // Verify: stable memory should not grow significantly (reuse occurred)
    assert!(
        stable_after <= stable_before + 1, // Allow minimal growth for structure overhead
        "Stable memory should not grow when reusing reclaimed buckets"
    );
}
