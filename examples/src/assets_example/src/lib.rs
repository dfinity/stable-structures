//! An example showcasing how you can store assets using a BTreeMap.
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager, VirtualMemory};
use ic_stable_structures::{DefaultMemoryImpl, StableBTreeMap};
use std::cell::RefCell;

type Memory = VirtualMemory<DefaultMemoryImpl>;

thread_local! {
    // The memory manager is used for simulating multiple memories. Given a `MemoryId` it can
    // return a memory that can be used by stable structures.
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));

    // Initialize a V2 BTreeMap that supports unbounded keys and values.
    static ASSETS: RefCell<StableBTreeMap<String, Vec<u8>, Memory>> = RefCell::new(
        StableBTreeMap::init(
            MEMORY_MANAGER.with(|m| m.borrow().get(MemoryId::new(0))),
        )
    );
}

#[ic_cdk::post_upgrade]
fn post_upgrade() {
    ASSETS.with(|p| drop(p.borrow()));
}

/// Retrieves the value associated with the given key if it exists.
#[ic_cdk_macros::query]
fn get(key: String) -> Option<Vec<u8>> {
    ASSETS.with(|p| p.borrow().get(&key))
}

/// Inserts an asset's name and value in the map, returning the previous value.
#[ic_cdk_macros::update]
fn insert(key: String, value: Vec<u8>) -> Option<Vec<u8>> {
    ASSETS.with(|p| p.borrow_mut().insert(key, value))
}
