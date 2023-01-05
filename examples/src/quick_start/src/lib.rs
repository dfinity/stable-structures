//! An example showcasing how stable structures, and specifically StableBTreeMap, can be used in
//! production alongside other state that is stored on the heap and is serialized/deserialized on
//! every upgrade.
//!
//! This example showcases how you can include stable structures in your projects. For simpler
//! examples, checkout the other examples in the `examples` directory.
use ic_cdk_macros::{post_upgrade, pre_upgrade, query, update};
use ic_stable_structures::{writer::Writer, Memory as _, StableBTreeMap};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
mod memory;
use memory::Memory;

// The state of the canister.
#[derive(Serialize, Deserialize)]
struct State {
    // Data that lives on the heap.
    // This is an example for data that would need to be serialized/deserialized
    // on every upgrade for it to be persisted.
    data_on_the_heap: Vec<u8>,

    // An example `StableBTreeMap`. Data stored in `StableBTreeMap` doesn't need to
    // be serialized/deserialized in upgrades, so we tell serde to skip it.
    #[serde(skip, default = "init_stable_data")]
    stable_data: StableBTreeMap<u128, u128, Memory>,
}

thread_local! {
    static STATE: RefCell<State> = RefCell::new(State::default());
}

// Retrieves the value associated with the given key in the stable data if it exists.
#[query]
fn stable_get(key: u128) -> Option<u128> {
    STATE.with(|s| s.borrow().stable_data.get(&key))
}

// Inserts an entry into the map and returns the previous value of the key from stable data
// if it exists.
#[update]
fn stable_insert(key: u128, value: u128) -> Option<u128> {
    STATE
        .with(|s| s.borrow_mut().stable_data.insert(key, value))
        .unwrap()
}

// Sets the data that lives on the heap.
#[update]
fn set_heap_data(data: Vec<u8>) {
    STATE.with(|s| s.borrow_mut().data_on_the_heap = data);
}

// Retrieves the data that lives on the heap.
#[query]
fn get_heap_data() -> Vec<u8> {
    STATE.with(|s| s.borrow().data_on_the_heap.clone())
}

// A pre-upgrade hook for serializing the data stored on the heap.
#[pre_upgrade]
fn pre_upgrade() {
    // Serialize the state.
    // This example is using CBOR, but you can use any data format you like.
    let mut state_bytes = vec![];
    STATE.with(|s| ciborium::ser::into_writer(&*s.borrow(), &mut state_bytes))
        .expect("failed to encode state");

    // Write the length of the serialized bytes to memory, followed by the
    // by the bytes themselves.
    let len = state_bytes.len() as u32;
    let mut memory = memory::get_upgrades_memory();
    let mut writer = Writer::new(&mut memory, 0);
    writer.write(&len.to_le_bytes()).unwrap();
    writer.write(&state_bytes).unwrap()
}

// A post-upgrade hook for deserializing the data back into the heap.
#[post_upgrade]
fn post_upgrade() {
    let memory = memory::get_upgrades_memory();

    // Read the length of the state bytes.
    let mut state_len_bytes = [0; 4];
    memory.read(0, &mut state_len_bytes);
    let state_len = u32::from_le_bytes(state_len_bytes) as usize;

    // Read the bytes
    let mut state_bytes = vec![0; state_len];
    memory.read(4, &mut state_bytes);

    // Deserialize and set the state.
    let state = ciborium::de::from_reader(&*state_bytes).expect("failed to decode state");
    STATE.with(|s| {
        *s.borrow_mut() = state
    });
}

fn init_stable_data() -> StableBTreeMap<u128, u128, Memory> {
    StableBTreeMap::init(crate::memory::get_stable_btree_memory())
}

impl Default for State {
    fn default() -> Self {
        Self {
            data_on_the_heap: vec![],
            stable_data: init_stable_data(),
        }
    }
}

