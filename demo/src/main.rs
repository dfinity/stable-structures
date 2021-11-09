//! Demo using a stable hashmap.
use ic_cdk::api::stable;
use ic_cdk_macros::*;
use stable_structures::allocator::mock_allocator::MockAllocator;
use stable_structures::{HashMap, Memory};
use std::cell::RefCell;
use std::convert::TryInto;
use std::sync::Arc;

struct State {
    map: RefCell<HashMap<StableMemory, MockAllocator<StableMemory>>>,
}

impl State {
    fn new() -> Self {
        ic_cdk::print("in State::new");
        let allocator = Arc::new(MockAllocator::new(StableMemory).unwrap());
        Self {
            map: RefCell::new(HashMap::new(allocator, StableMemory, 10).unwrap()),
        }
    }
}

thread_local! {
    static STATE: State = State::new();
}

#[pre_upgrade]
fn pre_upgrade() {
    ic_cdk::print("Running pre upgrade.");
    STATE.with(|s| {
        // Store the data we need to be able to recover the state once we upgrade.
        // In this case, the only data we need is the address of the hashmap.
        //
        // For more sophisticated states, we can use something like protobuf or
        // candid here.
        let root_data: Vec<u8> = s.map.borrow().own_address.to_le_bytes().to_vec();

        // The root data is written to stable memory and a pointer to this data
        // is stored in address 0 of stable memory.
        let allocator = MockAllocator::new(StableMemory).unwrap();
        stable_structures::write_root_data(&StableMemory, &allocator, &root_data)
    });
    ic_cdk::print("pre upgrade complete.");
}

#[post_upgrade]
fn post_upgrade() {
    ic_cdk::print("Running post upgrade.");
    STATE.with(|s| {
        // Read the root data stored in pre_upgrade. There is a pointer to the root
        // data stored in address 0 of stable memory.
        let root_data = stable_structures::read_root_data(&StableMemory).unwrap();

        // The root data in this case is simply the address of the hashmap, which
        // we can now use to reinitialize it.
        // TODO: Properly deallocate the hashmap that we're replacing.
        let allocator = Arc::new(MockAllocator::new(StableMemory).unwrap());
        s.map.replace(
            HashMap::load(
                allocator.clone(),
                StableMemory,
                u32::from_le_bytes(root_data.try_into().unwrap()),
            )
            .unwrap(),
        );
    });
    ic_cdk::print("post upgrade complete.");
}

#[update]
fn insert(key: Vec<u8>, value: Vec<u8>) {
    STATE.with(|s| {
        s.map.borrow_mut().insert(&key, &value);
    });
}

#[derive(candid::CandidType)]
enum GetResult {
    Ok(Vec<u8>),
    NotFound,
}

#[query]
fn get(key: Vec<u8>) -> GetResult {
    STATE.with(|s| {
        s.map
            .borrow()
            .get(&key)
            .map(GetResult::Ok)
            .unwrap_or(GetResult::NotFound)
    })
}

#[update]
fn remove(key: Vec<u8>) -> GetResult {
    STATE.with(|s| {
        s.map
            .borrow_mut()
            .remove(&key)
            .map(GetResult::Ok)
            .unwrap_or(GetResult::NotFound)
    })
}

fn main() {}

// A wrapper around the stable memory.
#[derive(Clone)]
struct StableMemory;

impl Memory for StableMemory {
    fn size(&self) -> u32 {
        stable::stable_size()
    }

    fn grow(&self, pages: u32) -> i32 {
        match stable::stable_grow(pages) {
            Ok(x) => x as i32,
            Err(_) => -1,
        }
    }

    fn read(&self, offset: u32, dst: &mut [u8]) {
        stable::stable_read(offset, dst)
    }

    fn write(&self, offset: u32, src: &[u8]) {
        stable::stable_write(offset, src)
    }
}
