use ic_stable_structures::memory_manager::{MemoryId, MemoryManager, VirtualMemory};
use ic_stable_structures::{BoundedStorable, DefaultMemoryImpl, StableBTreeMap, Storable};
use std::cell::RefCell;

type Memory = VirtualMemory<DefaultMemoryImpl>;

// `StableBTreeMap` requires specifying the maximum size in bytes that keys/values can hold. An
// entry in the map always takes up the maximum size in memory (i.e. MAX_KEY_SIZE + MAX_VALUE_SIZE),
// so you shouldn't specify sizes here that are larger than necessary.
//
// If your entries vary a lot in size, consider bucketizing them. For instance, you can create two
// different maps, one for holding "small" entries, and another for holding "large" entries.
const MAX_USER_NAME_SIZE: u32 = 10;
const MAX_USER_DATA_SIZE: u32 = 100;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
struct UserName(String);

impl Storable for UserName {
    fn to_bytes(&self) -> std::borrow::Cow<[u8]> {
        // String already implements `Storable`.
        self.0.to_bytes()
    }

    fn from_bytes(bytes: std::borrow::Cow<[u8]>) -> Self {
        Self(String::from_bytes(bytes))
    }
}

impl BoundedStorable for UserName {
    const MAX_SIZE: u32 = MAX_USER_NAME_SIZE;
    const IS_FIXED_SIZE: bool = false;
}

struct UserData(Vec<u8>);

impl Storable for UserData {
    fn to_bytes(&self) -> std::borrow::Cow<[u8]> {
        // Vec<u8> already implements `Storable`.
        self.0.to_bytes()
    }

    fn from_bytes(bytes: std::borrow::Cow<[u8]>) -> Self {
        Self(<Vec<u8>>::from_bytes(bytes))
    }
}

impl BoundedStorable for UserData {
    const MAX_SIZE: u32 = MAX_USER_DATA_SIZE;
    const IS_FIXED_SIZE: bool = false;
}

thread_local! {
    // The memory manager is used for simulating multiple memories. Given a `MemoryId` it can
    // return a memory that can be used by stable structures.
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));

    // Initialize a `StableBTreeMap` with `MemoryId(0)`.
    static MAP: RefCell<StableBTreeMap<UserName, UserData, Memory>> = RefCell::new(
        StableBTreeMap::init(
            MEMORY_MANAGER.with(|m| m.borrow().get(MemoryId::new(0))),
        )
    );
}

// Retrieves the value associated with the given key if it exists.
#[ic_cdk_macros::query]
fn get(key: String) -> Option<Vec<u8>> {
    MAP.with(|p| p.borrow().get(&UserName(key)).map(|v| v.0))
}

// Inserts an entry into the map and returns the previous value of the key if it exists.
#[ic_cdk_macros::update]
fn insert(key: String, value: Vec<u8>) -> Option<Vec<u8>> {
    MAP.with(|p| p.borrow_mut().insert(UserName(key), UserData(value)))
        .unwrap()
        .map(|v| v.0)
}
