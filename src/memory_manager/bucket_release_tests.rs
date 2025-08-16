//! Tests demonstrating bucket release efficiency in migration scenarios.
//!
//! Common pattern: User populates memory A, reads all data into heap memory,
//! clears A, then populates memory B. Without bucket release, B cannot reuse
//! A's buckets, causing memory waste. With bucket release, B can reuse A's
//! buckets, preventing memory growth.

use super::{MemoryId, MemoryManager};
use crate::{btreemap::BTreeMap, vec_mem::VectorMemory, Memory};

/// Helper function to create a blob that triggers bucket allocation
fn blob() -> Vec<u8> {
    vec![42u8; 2000] // 2KB blob
}

#[test]
fn migration_without_release_wastes_buckets() {
    // Scenario: Populate A → Clear A without bucket release → Populate B
    // Result: B cannot reuse A's buckets, causing memory waste (growth)
    let (a, b) = (MemoryId(0), MemoryId(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate in A
    let mut a_map = BTreeMap::init(mm.get(a));
    for i in 0u64..50 {
        a_map.insert(i, blob());
    }

    // Clear A without releasing buckets
    a_map.clear_new();
    let stable_before = mock_stable_memory.size();

    // Allocate in B → should need new buckets since A's aren't released
    let mut b_map = BTreeMap::init(mm.get(b));
    for i in 0u64..50 {
        b_map.insert(i, blob());
    }
    let stable_after = mock_stable_memory.size();

    // Verify: maps correct, stable memory grew (waste)
    assert_eq!(a_map.len(), 0);
    assert_eq!(b_map.len(), 50);
    assert!(stable_after > stable_before, "Stable memory grew (waste)");
}

#[test]
fn migration_with_release_reuses_buckets() {
    // Scenario: Populate A → Clear A with bucket release → Populate B
    // Result: B reuses A's released buckets, preventing memory waste (no growth)
    let (a, b) = (MemoryId(0), MemoryId(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate in A
    let mut a_map = BTreeMap::init(mm.get(a));
    for i in 0u64..50 {
        a_map.insert(i, blob());
    }

    // Clear A and release its buckets
    a_map.clear_new();
    let released_buckets = mm.try_release_virtual_memory_buckets(a);
    assert!(released_buckets > 0);
    let stable_before = mock_stable_memory.size();

    // Allocate in B → should reuse A's released buckets
    let mut b_map = BTreeMap::init(mm.get(b));
    for i in 0u64..50 {
        b_map.insert(i, blob());
    }
    let stable_after = mock_stable_memory.size();

    // Verify: maps correct, stable memory unchanged (reuse)
    assert_eq!(a_map.len(), 0);
    assert_eq!(b_map.len(), 50);
    assert!(
        stable_after <= stable_before,
        "Stable memory unchanged (reuse)"
    );
}

#[test]
fn release_empty_memory_returns_zero() {
    // Test: Releasing buckets from unused memory should return 0
    let memory_id = MemoryId(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Try to release buckets from empty memory
    let released_buckets = mm.try_release_virtual_memory_buckets(memory_id);

    // Should return 0 since no buckets were allocated
    assert_eq!(released_buckets, 0, "Empty memory should release 0 buckets");
}

#[test]
fn double_release_returns_zero_second_time() {
    // Test: Releasing the same memory twice should return 0 on second attempt
    let memory_id = MemoryId(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Populate memory to create buckets
    let mut map = BTreeMap::init(mm.get(memory_id));
    for i in 0u64..50 {
        map.insert(i, blob());
    }

    // Clear and release buckets
    map.clear_new();
    let first_release = mm.try_release_virtual_memory_buckets(memory_id);
    assert!(first_release > 0, "First release should return >0 buckets");

    // Try to release again
    let second_release = mm.try_release_virtual_memory_buckets(memory_id);
    assert_eq!(second_release, 0, "Second release should return 0 buckets");
}

#[test]
fn release_only_affects_target_memory() {
    // Test: Releasing memory A should not affect memory B's allocation ability
    let (a, b) = (MemoryId(0), MemoryId(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Populate both memories
    let mut a_map = BTreeMap::init(mm.get(a));
    let mut b_map = BTreeMap::init(mm.get(b));
    for i in 0u64..30 {
        a_map.insert(i, blob());
        b_map.insert(i, blob());
    }

    // Clear and release A's buckets
    a_map.clear_new();
    let released_buckets = mm.try_release_virtual_memory_buckets(a);
    assert!(released_buckets > 0, "Should release A's buckets");

    // Verify B can still allocate new data (its buckets weren't affected)
    for i in 30u64..60 {
        b_map.insert(i, blob());
    }

    // Verify final state
    assert_eq!(a_map.len(), 0);
    assert_eq!(b_map.len(), 60);
}

#[test]
fn multiple_release_cycles() {
    // Test: Multiple populate→clear→release cycles should work consistently
    let memory_id = MemoryId(0);
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // Perform several cycles of populate→clear→release
    for cycle in 0..27 {
        // Populate memory
        let mut map = BTreeMap::init(mm.get(memory_id));
        for i in 0u64..40 {
            map.insert(i, blob());
        }

        // Clear and release buckets
        map.clear_new();
        let released_buckets = mm.try_release_virtual_memory_buckets(memory_id);

        assert!(
            released_buckets > 0,
            "Cycle {} should release >0 buckets, got {}",
            cycle,
            released_buckets
        );
    }
}
