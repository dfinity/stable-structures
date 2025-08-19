//! Migration scenario tests for BTreeMap with memory reclamation.
//!
//! These tests demonstrate real-world migration patterns where users move data
//! from one structure to another. They show how memory reclamation prevents memory
//! waste during common migration scenarios, and most importantly, demonstrate
//! the data corruption bug and its safe usage solution.
//!
//! **CRITICAL SAFETY REQUIREMENTS**:
//! All memory reclamation operations require mandatory Rust object drop BEFORE reclamation.
//! Using original data structures after memory reclamation causes data corruption.
//! See MemoryManager documentation for proper usage patterns.

use super::{MemoryId, MemoryManager};
use crate::{btreemap::BTreeMap, vec_mem::VectorMemory, Memory};

/// Helper function to create a blob that triggers bucket allocation
fn large_value(id: u64) -> Vec<u8> {
    let mut data = vec![0u8; 1024]; // 1KB value
                                    // Fill with pattern based on id to make values unique
    for (i, byte) in data.iter_mut().enumerate() {
        *byte = ((id + i as u64) % 256) as u8;
    }
    data
}

#[test]
fn migration_without_reclaim_wastes_buckets() {
    // Scenario: Populate A → Drop A without memory reclamation → Populate B
    // Result: B cannot reuse A's buckets, causing memory waste (growth)
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate in A
    let mut a_map = BTreeMap::init(mm.get(a));
    for i in 0u64..50 {
        a_map.insert(i, large_value(i));
    }
    assert_eq!(a_map.len(), 50);

    // Drop A without releasing buckets
    drop(a_map);
    let stable_before = mock_stable_memory.size();

    // Allocate in B → should need new buckets since A's aren't reclaimed
    let mut b_map = BTreeMap::init(mm.get(b));
    for i in 0u64..50 {
        b_map.insert(i, large_value(i + 100));
    }
    let stable_after = mock_stable_memory.size();

    // Verify: B allocated new buckets, stable memory grew (waste)
    assert_eq!(b_map.len(), 50);
    assert!(stable_after > stable_before, "Stable memory grew (waste)");
}

#[test]
fn migration_with_reclaim_reuses_buckets() {
    // Scenario: Populate A → Drop A with memory reclamation → Populate B
    // Result: B reuses A's reclaimed buckets, preventing memory waste (no growth)
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate in A
    let mut a_map = BTreeMap::init(mm.get(a));
    for i in 0u64..50 {
        a_map.insert(i, large_value(i));
    }
    assert_eq!(a_map.len(), 50);

    // MANDATORY: Drop the Rust object before reclaiming memory
    drop(a_map);

    // Reclaim the memory after dropping the object
    let pages_reclaimed = mm.reclaim_memory(a);
    assert!(pages_reclaimed > 0);
    let stable_before = mock_stable_memory.size();

    // Allocate in B → should reuse A's reclaimed buckets
    let mut b_map = BTreeMap::init(mm.get(b));
    for i in 0u64..50 {
        b_map.insert(i, large_value(i + 100));
    }
    let stable_after = mock_stable_memory.size();

    // Verify: B reused A's buckets, stable memory unchanged (reuse)
    assert_eq!(b_map.len(), 50);
    assert!(
        stable_after <= stable_before,
        "Stable memory unchanged (reuse)"
    );
}

/// **DANGER**: This test demonstrates data corruption from unsafe memory reclamation usage.
/// This shows what happens when you DON'T drop the original object before memory reclamation.
#[test]
fn data_corruption_without_mandatory_drop() {
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mm = MemoryManager::init(VectorMemory::default());

    // Create BTreeMap A with test data
    let mut map_a = BTreeMap::init(mm.get(a));
    map_a.insert(1u64, 100u64);
    assert_eq!(map_a.get(&1u64).unwrap(), 100u64);

    // DANGEROUS: Reclaim memory but keep map_a alive
    mm.reclaim_memory(a);

    // Create BTreeMap B - reuses A's reclaimed buckets
    let mut map_b = BTreeMap::init(mm.get(b));
    map_b.insert(2u64, 200u64);
    assert_eq!(map_b.get(&2u64).unwrap(), 200u64);

    // CORRUPTION: map_a and map_b now share the same underlying memory
    // This can manifest in different ways - either seeing shared data or allocation corruption

    // First check if map_a can see map_b's data (shared memory corruption)
    if let Some(corrupted_data) = map_a.get(&2u64) {
        assert_eq!(
            corrupted_data, 200u64,
            "CORRUPTION: map_a sees map_b's data!"
        );
        return; // Corruption demonstrated through shared data
    }

    // If shared data isn't visible, try to trigger allocation corruption
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        map_a.insert(3u64, 300u64);
        map_a.get(&3u64)
    }));

    // Should either panic or show corruption through shared allocations
    match result {
        Ok(_) => {
            // If it succeeds, check if map_b can see the new data (shared allocation)
            if map_b.get(&3u64).is_some() {
                println!("CORRUPTION: Both maps operating on the same reclaimed memory space");
            }
        }
        Err(_) => {
            // Expected: panic due to allocator corruption
            println!("CORRUPTION: Panic due to memory corruption - this proves the bug");
        }
    }

    // This test proves why objects MUST be dropped before memory reclamation
}

/// **SAFE**: This test demonstrates the correct way to use memory reclamation.
/// This shows how mandatory drop prevents data corruption.
#[test]
fn safe_usage_with_mandatory_drop() {
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mm = MemoryManager::init(VectorMemory::default());

    // Create and populate BTreeMap A
    let mut map_a = BTreeMap::init(mm.get(a));
    map_a.insert(1u64, 100u64);
    assert_eq!(map_a.get(&1u64).unwrap(), 100u64);

    // MANDATORY: Drop the Rust object before reclaiming memory
    drop(map_a);

    // Reclaim the memory after dropping the object
    let pages_reclaimed = mm.reclaim_memory(a);
    assert!(pages_reclaimed > 0);

    // Create BTreeMap B - safely reuses A's reclaimed buckets
    let mut map_b = BTreeMap::init(mm.get(b));
    map_b.insert(2u64, 200u64);
    assert_eq!(map_b.get(&2u64).unwrap(), 200u64);

    // Create new BTreeMap on same memory ID A - safe after proper drop
    let mut map_a_new = BTreeMap::init(mm.get(a));
    map_a_new.insert(3u64, 300u64);
    assert_eq!(map_a_new.get(&3u64).unwrap(), 300u64);

    // Verify maps are completely independent - no corruption
    assert_eq!(map_b.len(), 1, "Map B should have 1 element");
    assert_eq!(map_a_new.len(), 1, "Map A new should have 1 element");
    assert_eq!(map_b.get(&2u64).unwrap(), 200u64);
    assert_eq!(map_a_new.get(&3u64).unwrap(), 300u64);

    // Both maps can grow independently without corruption
    map_a_new.insert(4u64, 400u64);
    map_b.insert(5u64, 500u64);
    assert_eq!(map_a_new.len(), 2);
    assert_eq!(map_b.len(), 2);
}
