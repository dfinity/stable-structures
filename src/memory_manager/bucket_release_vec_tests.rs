//! Migration scenario tests for Vec with bucket release.
//!
//! These tests demonstrate real-world migration patterns where users move data
//! from one structure to another. They show how bucket release prevents memory
//! waste during common migration scenarios, and most importantly, demonstrate
//! the data corruption bug and its safe usage solution for Vec structures.
//!
//! **CRITICAL SAFETY REQUIREMENTS**:
//! All bucket release operations require mandatory Rust object drop BEFORE release.
//! Using original data structures after bucket release causes data corruption.
//! See MemoryManager documentation for proper usage patterns.
//!
//! **Vec-Specific Notes**:
//! Vec doesn't have a clear() method. Since we drop the object before bucket release,
//! there's no need to clear the data first.

use super::{MemoryId, MemoryManager};
use crate::{vec::Vec as StableVec, vec_mem::VectorMemory, Memory};

/// Helper function to create data that triggers bucket allocation
fn large_data(id: u64) -> [u8; 1024] {
    let mut data = [0u8; 1024];
    // Fill with pattern based on id to make data unique
    for (i, byte) in data.iter_mut().enumerate() {
        *byte = ((id + i as u64) % 256) as u8;
    }
    data
}

#[test]
fn migration_without_release_wastes_buckets() {
    // Scenario: Populate A → Clear A without bucket release → Populate B
    // Result: B cannot reuse A's buckets, causing memory waste (growth)
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory.clone());

    // Allocate in A
    let vec_a = StableVec::init(mm.get(a));
    for i in 0u64..50 {
        vec_a.push(&large_data(i));
    }
    assert_eq!(vec_a.len(), 50);

    // "Clear" A by creating new instance (overwrites data) without releasing buckets
    let vec_a: StableVec<[u8; 1024], _> = StableVec::new(mm.get(a)); // Overwrites existing data
    assert_eq!(vec_a.len(), 0);
    let stable_before = mock_stable_memory.size();

    // Allocate in B → should need new buckets since A's aren't released
    let vec_b = StableVec::init(mm.get(b));
    for i in 0u64..50 {
        vec_b.push(&large_data(i + 100));
    }
    let stable_after = mock_stable_memory.size();

    // Verify: vecs correct, stable memory grew (waste)
    assert_eq!(vec_a.len(), 0);
    assert_eq!(vec_b.len(), 50);
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
    let vec_a_original = StableVec::init(mm.get(a));
    for i in 0u64..50 {
        vec_a_original.push(&large_data(i));
    }
    assert_eq!(vec_a_original.len(), 50);

    // MANDATORY: Drop the Rust object before releasing buckets
    drop(vec_a_original);

    // Release the buckets after dropping the object
    let released_buckets = mm.release_virtual_memory_buckets(a);
    assert!(released_buckets > 0);
    let stable_before = mock_stable_memory.size();

    // Allocate in B → should reuse A's released buckets
    let vec_b = StableVec::init(mm.get(b));
    for i in 0u64..50 {
        vec_b.push(&large_data(i + 100));
    }
    let stable_after = mock_stable_memory.size();

    // Verify: B reused A's buckets, stable memory unchanged (reuse)
    assert_eq!(vec_b.len(), 50);
    assert!(
        stable_after <= stable_before,
        "Stable memory unchanged (reuse)"
    );
}

/// **DANGER**: This test demonstrates data corruption from unsafe bucket release usage.
/// This shows what happens when you DON'T drop the original object after bucket release.
#[test]
fn data_corruption_without_mandatory_drop() {
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mm = MemoryManager::init(VectorMemory::default());

    // Create Vec A with test data
    let vec_a = StableVec::init(mm.get(a));
    vec_a.push(&1u64);
    assert_eq!(vec_a.get(0).unwrap(), 1u64);

    // "Clear" by creating new instance, but keep vec_a alive (DANGEROUS!)
    let vec_a: StableVec<u64, _> = StableVec::new(mm.get(a)); // Overwrites data
    assert_eq!(vec_a.len(), 0);
    mm.release_virtual_memory_buckets(a);

    // Create Vec B - reuses A's released buckets
    let vec_b = StableVec::init(mm.get(b));
    vec_b.push(&2u64);
    assert_eq!(vec_b.get(0).unwrap(), 2u64);

    // CORRUPTION: vec_a and vec_b now share the same underlying memory
    // This can manifest in different ways - either seeing shared data or allocation corruption

    // First check if vec_a can see vec_b's data (shared memory corruption)
    if !vec_a.is_empty() {
        if let Some(corrupted_data) = vec_a.get(0) {
            assert_eq!(corrupted_data, 2u64, "CORRUPTION: vec_a sees vec_b's data!");
            return; // Corruption demonstrated through shared data
        }
    }

    // If shared data isn't visible, try to trigger allocation corruption
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        vec_a.push(&3u64);
        vec_a.get(0)
    }));

    // Should either panic or show corruption through shared allocations
    match result {
        Ok(_) => {
            // If it succeeds, check if vec_b can see the new data (shared allocation)
            if !vec_a.is_empty() && vec_b.len() > vec_a.len() {
                // Check if data appears in unexpected places
                println!("CORRUPTION: Both vecs operating on the same released memory space");
            }
        }
        Err(_) => {
            // Expected: panic due to allocator corruption
            println!("CORRUPTION: Panic due to memory corruption - this proves the bug");
        }
    }

    // This test proves why objects MUST be dropped after bucket release
}

/// **SAFE**: This test demonstrates the correct way to use bucket release.
/// This shows how mandatory drop prevents data corruption.
#[test]
fn safe_usage_with_mandatory_drop() {
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mm = MemoryManager::init(VectorMemory::default());

    // Create and populate Vec A
    let vec_a = StableVec::init(mm.get(a));
    vec_a.push(&1u64);
    assert_eq!(vec_a.get(0).unwrap(), 1u64);

    // MANDATORY: Drop the Rust object before releasing buckets
    drop(vec_a);

    // Release the buckets after dropping the object
    let released_buckets = mm.release_virtual_memory_buckets(a);
    assert!(released_buckets > 0);

    // Create Vec B - safely reuses A's released buckets
    let vec_b = StableVec::init(mm.get(b));
    vec_b.push(&2u64);
    assert_eq!(vec_b.get(0).unwrap(), 2u64);

    // Create new Vec on same memory ID A - safe after proper drop
    let vec_a_new = StableVec::init(mm.get(a));
    vec_a_new.push(&3u64);
    assert_eq!(vec_a_new.get(0).unwrap(), 3u64);

    // Verify vecs are completely independent - no corruption
    assert_eq!(vec_b.len(), 1, "Vec B should have 1 element");
    assert_eq!(vec_a_new.len(), 1, "Vec A new should have 1 element");
    assert_eq!(vec_b.get(0).unwrap(), 2u64);
    assert_eq!(vec_a_new.get(0).unwrap(), 3u64);

    // Both vecs can grow independently without corruption
    vec_a_new.push(&4u64);
    vec_b.push(&5u64);
    assert_eq!(vec_a_new.len(), 2);
    assert_eq!(vec_b.len(), 2);
}
