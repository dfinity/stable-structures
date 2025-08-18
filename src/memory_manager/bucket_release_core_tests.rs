//! Core bucket release functionality tests for MemoryManager.
//!
//! These tests verify the basic memory management operations without dependency
//! on specific data structures. They test the fundamental bucket allocation,
//! release, and reuse mechanisms.

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
    map.clear_new(); // Clear the structure but keep buckets allocated
}

#[test]
fn release_empty_memory_returns_zero() {
    // Test: Releasing buckets from unused memory should return 0
    let memory_id = MemoryId::new(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Try to release buckets from empty memory
    let released_buckets = mm.release_virtual_memory_buckets(memory_id);

    // Should return 0 since no buckets were allocated
    assert_eq!(released_buckets, 0, "Empty memory should release 0 buckets");
}

#[test]
fn double_release_returns_zero_second_time() {
    // Test: Releasing the same memory twice should return 0 on second attempt
    let memory_id = MemoryId::new(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Allocate buckets and clear structure
    allocate_buckets_via_btreemap(&mm, memory_id, 50);

    // Release buckets
    let first_release = mm.release_virtual_memory_buckets(memory_id);
    assert!(first_release > 0, "First release should return >0 buckets");

    // Try to release again
    let second_release = mm.release_virtual_memory_buckets(memory_id);
    assert_eq!(second_release, 0, "Second release should return 0 buckets");
}

#[test]
fn release_only_affects_target_memory() {
    // Test: Releasing memory A should not affect memory B's buckets
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Allocate buckets in both memories
    allocate_buckets_via_btreemap(&mm, a, 30);
    allocate_buckets_via_btreemap(&mm, b, 30);

    // Release A's buckets
    let released_buckets = mm.release_virtual_memory_buckets(a);
    assert!(released_buckets > 0, "Should release A's buckets");

    // Verify B still has its buckets (can't be released again)
    let b_release_attempt = mm.release_virtual_memory_buckets(b);
    assert!(
        b_release_attempt > 0,
        "B should still have releasable buckets"
    );
}

#[test]
fn multiple_release_cycles() {
    // Test: Multiple allocate→release cycles should work consistently
    let memory_id = MemoryId::new(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Perform several cycles of allocate→release
    for cycle in 0..5 {
        // Allocate buckets
        allocate_buckets_via_btreemap(&mm, memory_id, 40);

        // Release buckets
        let released_buckets = mm.release_virtual_memory_buckets(memory_id);

        assert!(
            released_buckets > 0,
            "Cycle {} should release >0 buckets, got {}",
            cycle,
            released_buckets
        );
    }
}

#[test]
fn bucket_reuse_prevents_memory_growth() {
    // Test: Released buckets are actually reused by subsequent allocations
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate buckets in A
    allocate_buckets_via_btreemap(&mm, a, 50);

    // Release A's buckets
    let released_buckets = mm.release_virtual_memory_buckets(a);
    assert!(released_buckets > 0);
    let stable_before = mock_stable_memory.size();

    // Allocate same amount in B → should reuse A's released buckets
    allocate_buckets_via_btreemap(&mm, b, 50);
    let stable_after = mock_stable_memory.size();

    // Verify: stable memory should not grow significantly (reuse occurred)
    assert!(
        stable_after <= stable_before + 1, // Allow minimal growth for structure overhead
        "Stable memory should not grow when reusing released buckets"
    );
}
