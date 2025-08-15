use super::{MemoryId, MemoryManager};
use crate::{btreemap::BTreeMap, vec_mem::VectorMemory, Memory};

#[test]
fn test_try_release_virtual_memory_buckets_empty_memory_no_release() {
    // Arrange
    let id = MemoryId(0);
    let mem = VectorMemory::default();
    let mm = MemoryManager::init(mem);

    // Act
    let released = mm.try_release_virtual_memory_buckets(id);

    // Assert
    assert_eq!(released, 0, "sanity: no buckets released");
    assert_eq!(mm.get(id).size(), 0, "sanity: no pages allocated");
}

#[test]
fn test_try_release_virtual_memory_buckets_release_after_clear_reclaims_one_bucket() {
    // Arrange
    let id = MemoryId(0);
    let mem = VectorMemory::default();
    let mm = MemoryManager::init(mem);
    let mut map: BTreeMap<u64, u64, _> = BTreeMap::init(mm.get(id));

    // Act
    map.insert(1, 1);
    assert_eq!(mm.get(id).size(), 1, "sanity: one page allocated");

    map.clear_new();
    let released = mm.try_release_virtual_memory_buckets(id);

    // Assert
    assert_eq!(released, 1, "sanity: one bucket released");
    assert_eq!(mm.get(id).size(), 0, "sanity: no pages allocated");
}

#[test]
fn double_release_is_idempotent() {
    // Arrange
    let id = MemoryId(0);
    let mem = VectorMemory::default();
    let mm = MemoryManager::init(mem);
    let mut map: BTreeMap<u64, u64, _> = BTreeMap::init(mm.get(id));

    // Act
    map.insert(1, 2);
    assert_eq!(mm.get(id).size(), 1, "sanity: one page allocated");

    map.clear_new();
    let _ = mm.try_release_virtual_memory_buckets(id); // first release

    let released_again = mm.try_release_virtual_memory_buckets(id); // second release

    // Assert
    assert_eq!(released_again, 0, "sanity: no buckets released");
    assert_eq!(mm.get(id).size(), 0, "sanity: no pages allocated");
}

#[test]
fn buckets_can_be_reused_after_release() {
    // Arrange
    let a = MemoryId(0);
    let b = MemoryId(1);
    let mem = VectorMemory::default();
    let mm = MemoryManager::init(mem);

    // Act — allocate in A, clear, release
    let mut map_a: BTreeMap<u64, u64, _> = BTreeMap::init(mm.get(a));
    map_a.insert(1, 1);
    map_a.clear_new();
    let _ = mm.try_release_virtual_memory_buckets(a);

    // Assert — A is empty after release
    assert_eq!(mm.get(a).size(), 0, "sanity: no pages allocated");

    // Act — allocate in B, should succeed and use a bucket
    let mut map_b: BTreeMap<u64, u64, _> = BTreeMap::init(mm.get(b));
    map_b.insert(2, 2);

    // Assert
    assert_eq!(
        map_b.get(&2),
        Some(2),
        "sanity: map B contains the correct value"
    );
    assert_eq!(mm.get(b).size(), 1, "sanity: one page allocated");
}
