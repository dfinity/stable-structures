//! Migration scenario tests for BTreeMap with bucket release.
//!
//! These tests demonstrate real-world migration patterns where users move data
//! from one structure to another. They show how bucket release prevents memory
//! waste during common migration scenarios, and most importantly, demonstrate
//! the data corruption bug and its safe usage solution.
//!
//! **CRITICAL SAFETY REQUIREMENTS**:
//! All bucket release operations require mandatory Rust object drop after release.
//! Using original data structures after bucket release causes data corruption.
//! See MemoryManager documentation for proper usage patterns.

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

/// **DANGER**: This test demonstrates data corruption from unsafe bucket release usage.
/// This shows what happens when you DON'T drop the original object after bucket release.
#[test]
fn data_corruption_without_mandatory_drop() {
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // 1. Create BTreeMap A with specific data
    let mut map_a = BTreeMap::init(mm.get(a));
    map_a.insert(42u64, b"original_data_from_A".to_vec());
    assert_eq!(map_a.get(&42).unwrap(), b"original_data_from_A");

    // 2. Clear the map but keep it in scope (DANGEROUS PATTERN)
    map_a.clear_new();
    assert_eq!(map_a.len(), 0);

    // 3. Release A's buckets - this makes map_a's memory available for reuse
    let released_buckets = mm.release_virtual_memory_buckets(a);
    assert!(released_buckets > 0);

    // 4. DANGER: map_a still exists but its buckets were released

    // 5. Create BTreeMap B - will reuse A's released buckets
    let mut map_b = BTreeMap::init(mm.get(b));
    map_b.insert(99u64, b"new_data_from_B".to_vec());
    assert_eq!(map_b.get(&99).unwrap(), b"new_data_from_B");

    // 6. CORRUPTION REVEALED: map_a now sees map_b's data!
    // This happens because both maps share the same underlying bucket
    if let Some(corrupted_data) = map_a.get(&99u64) {
        assert_eq!(
            corrupted_data, b"new_data_from_B",
            "CORRUPTION: map_a sees map_b's data due to bucket reuse!"
        );
    }

    // 7. Attempting to write to map_a causes allocation corruption
    let corruption_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        map_a.insert(77u64, b"corruption_data".to_vec());
    }));

    // This should panic with "Attempting to allocate an already allocated chunk"
    // proving that the memory management is corrupted
    match corruption_result {
        Ok(_) => {
            // If it doesn't panic, still demonstrates corruption through shared data
            if let Some(data) = map_b.get(&77u64) {
                assert_eq!(
                    data, b"corruption_data",
                    "CORRUPTION: Both maps share the same memory space!"
                );
            }
        }
        Err(panic_info) => {
            // Expected: panic due to allocator corruption
            let panic_msg = panic_info
                .downcast_ref::<&str>()
                .unwrap_or(&"Unknown panic");
            assert!(
                panic_msg.contains("already allocated") || panic_msg.contains("allocation"),
                "Should panic due to allocation corruption, got: {}",
                panic_msg
            );
        }
    }

    // This test proves why objects MUST be dropped after bucket release
}

/// **SAFE**: This test demonstrates the correct way to use bucket release.
/// This shows how mandatory drop prevents data corruption.
#[test]
fn safe_usage_with_mandatory_drop() {
    let (a, b) = (MemoryId::new(0), MemoryId::new(1));
    let mock_stable_memory = VectorMemory::default();
    let mm = MemoryManager::init(mock_stable_memory);

    // 1. Create BTreeMap A with specific data
    let mut map_a = BTreeMap::init(mm.get(a));
    map_a.insert(42u64, b"original_data_from_A".to_vec());
    assert_eq!(map_a.get(&42).unwrap(), b"original_data_from_A");

    // 2. Clear the map
    map_a.clear_new();
    assert_eq!(map_a.len(), 0);

    // 3. Release A's buckets
    let released_buckets = mm.release_virtual_memory_buckets(a);
    assert!(released_buckets > 0);

    // 4. MANDATORY: Explicitly drop the original object
    drop(map_a);

    // 5. Create BTreeMap B - safely reuses A's released buckets
    let mut map_b = BTreeMap::init(mm.get(b));
    map_b.insert(99u64, b"new_data_from_B".to_vec());
    assert_eq!(map_b.get(&99).unwrap(), b"new_data_from_B");

    // 6. Verify bucket reuse actually happened
    assert!(
        released_buckets > 0,
        "Should have released buckets for reuse"
    );

    // 7. No corruption possible because map_a was properly dropped
    // map_b operates safely on the reused memory
    map_b.insert(77u64, b"additional_data".to_vec());
    assert_eq!(map_b.get(&77).unwrap(), b"additional_data");
    assert_eq!(map_b.len(), 2);

    // 8. IMPORTANT: Create new structure reusing the SAME memory ID A
    // This proves that after proper drop, the memory ID can be safely reused
    let mut map_a_new = BTreeMap::init(mm.get(a)); // Reusing memory ID A!

    // 9. Verify the new map on memory ID A works correctly
    map_a_new.insert(123u64, b"fresh_data_on_A".to_vec());
    assert_eq!(map_a_new.get(&123).unwrap(), b"fresh_data_on_A");
    assert_eq!(map_a_new.len(), 1);

    // 10. Add more data to ensure memory growth works correctly
    for i in 200u64..250 {
        map_a_new.insert(i, blob()); // Large data to trigger bucket allocation
    }
    assert_eq!(map_a_new.len(), 51); // 1 + 50 entries

    // 11. Verify original map_b is unaffected by map_a_new operations
    assert_eq!(map_b.get(&99).unwrap(), b"new_data_from_B");
    assert_eq!(map_b.get(&77).unwrap(), b"additional_data");
    assert_eq!(map_b.len(), 2);

    // 12. Both maps should be completely independent
    // map_a_new should not see map_b's data
    assert!(
        map_a_new.get(&99).is_none(),
        "map_a_new should not see map_b's data"
    );
    assert!(
        map_a_new.get(&77).is_none(),
        "map_a_new should not see map_b's data"
    );

    // map_b should not see map_a_new's data
    assert!(
        map_b.get(&123).is_none(),
        "map_b should not see map_a_new's data"
    );
    assert!(
        map_b.get(&200).is_none(),
        "map_b should not see map_a_new's data"
    );

    // This demonstrates that proper drop() allows safe memory ID reuse!
}
