use candid::{CandidType, Decode, Deserialize, Encode};
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager, VirtualMemory};
use ic_stable_structures::{DefaultMemoryImpl, StableBTreeMap, Storable};
use std::{borrow::Cow, cell::RefCell};

type Memory = VirtualMemory<DefaultMemoryImpl>;

const MAX_KEY_SIZE: u32 = 8;
const MAX_VALUE_SIZE: u32 = 100;

#[derive(CandidType, Deserialize)]
struct UserProfile {
    age: u8,
    name: String,
}

// For a type to be used in a `StableBTreeMap`, it needs to implement the `Storable`
// trait, which specifies how the type can be serialized/deserialized.
//
// In this example, we're using candid to serialize/deserialize the struct, but you
// can use anything as long as you're maintaining backward-compatibility. The
// backward-compatibility allows you to change your struct over time (e.g. adding
// new fields).
//
// The `Storable` trait is already implemented for many common types (e.g. u64, String),
// so you can use those directly without implementing the `Storable` trait for them.
impl Storable for UserProfile {
    fn to_bytes(&self) -> std::borrow::Cow<[u8]> {
        Cow::Owned(Encode!(self).unwrap())
    }

    fn from_bytes(bytes: Vec<u8>) -> Self {
        Decode!(&bytes, Self).unwrap()
    }
}

thread_local! {
    // The memory manager is used for simulating multiple memories. Given a `MemoryId` it can
    // return a memory that can be used by stable structures.
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));

    static MAP: RefCell<StableBTreeMap<Memory, u64, UserProfile>> = RefCell::new(
        StableBTreeMap::init(
            MEMORY_MANAGER.with(|m| m.borrow().get(MemoryId::new(0))),
            MAX_KEY_SIZE,
            MAX_VALUE_SIZE
        )
    );
}

/// Retrieves the value associated with the given key if it exists.
#[ic_cdk_macros::query]
fn get(key: u64) -> Option<UserProfile> {
    MAP.with(|p| p.borrow().get(&key))
}

#[ic_cdk_macros::update]
fn insert(key: u64, value: UserProfile) -> Option<UserProfile> {
    MAP.with(|p| p.borrow_mut().insert(key, value)).unwrap()
}
