use ic_stable_structures::memory_manager::{ManagedMemory, MemoryId, MemoryManager};
use ic_stable_structures::{DefaultMemoryImpl, StableBTreeMap};
use std::cell::RefCell;

type Memory = ManagedMemory<DefaultMemoryImpl>;

// `StableBTreeMap` requires specifying the maximum size in bytes that keys/values can hold. An
// entry in the map always takes up the maximum size in memory (i.e. MAX_KEY_SIZE + MAX_VALUE_SIZE),
// so you shouldn't specify sizes here that are larger than necessary.
//
// If your entries vary a lot in size, consider bucketizing them. For instance, you can create two
// different maps, one for holding "small" entries, and another for holding "large" entries.
const MAX_KEY_SIZE: u32 = 10;
const MAX_VALUE_SIZE: u32 = 100;

thread_local! {
    // The memory manager is used for simulating multiple memories. Given a `MemoryId` it can
    // return a memory that can be used by stable structures.
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));

    // Initialize a `StableBTreeMap` with `MemoryId(0)`.
    static MAP: RefCell<StableBTreeMap<Memory, String, Vec<u8>>> = RefCell::new(
        StableBTreeMap::init(
            MEMORY_MANAGER.with(|m| m.borrow().get(MemoryId::new(0))),
            MAX_KEY_SIZE,
            MAX_VALUE_SIZE
        )
    );
}

// Retrieves the value associated with the given key if it exists.
#[ic_cdk_macros::query]
fn get(key: String) -> Option<Vec<u8>> {
    MAP.with(|p| p.borrow().get(&key))
}

// Inserts an entry into the map and returns the previous value of the key if it exists.
#[ic_cdk_macros::update]
fn insert(key: String, value: Vec<u8>) -> Option<Vec<u8>> {
    MAP.with(|p| p.borrow_mut().insert(key, value)).unwrap()
}
