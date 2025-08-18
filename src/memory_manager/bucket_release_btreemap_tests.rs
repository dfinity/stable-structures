//! Migration scenario tests for BTreeMap with bucket release.
//!
//! These tests demonstrate real-world migration patterns where users move data
//! from one structure to another. They show how bucket release prevents memory
//! waste during common migration scenarios.

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
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
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
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate in A
    let mut a_map = BTreeMap::init(mm.get(a));
    for i in 0u64..50 {
        a_map.insert(i, blob());
    }

    // Clear A and release its buckets
    a_map.clear_new();
    let released_buckets = mm.release_virtual_memory_buckets(a);
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
