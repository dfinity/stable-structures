use crate::btreemap::{
    node::{Version, CAPACITY},
    Node, NodeType,
};
use crate::types::Address;
use proptest::collection::btree_set as pset;
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

#[test]
fn can_upgrade_v1_into_v2() {
    let mem = make_memory();
    let address = Address::from(0);
    proptest!(|(
       entries in pset((pvec(0..u8::MAX, 0..10), pvec(0..u8::MAX, 0..10)), 0..CAPACITY),
    )| {
        // Create a node with arbitrary entries.
        let mut node = Node::<Vec<u8>>::new(address, NodeType::Leaf, 10, 10);
        let entries: Vec<_> = entries.into_iter().collect();

        // Insert entries into the node.
        for (idx, entry) in entries.iter().enumerate() {
            node.insert_entry(idx, entry.clone());
        }

        assert_eq!(node.entries(&mem), entries);

        // Save the node using the v1 layout.
        node.save_v1(&mem);

        // Loading the node using the v1 layout should preserve the entries.
        let mut node = Node::<Vec<u8>>::load(address, &mem, 10, 10);
        assert_eq!(node.entries(&mem), entries);
        assert_eq!(node.version, Version::V1.into());

        // Saving the node with the v2 layout should also work and preserve the entries.
        node.save_v2(&mem);
        let node = Node::<Vec<u8>>::load(Address::from(0), &mem, 10, 10);
        assert_eq!(node.entries(&mem), entries);
        assert_eq!(node.version, Version::V2.into());
    });
}

// Verifies that, if the key is > u16::MAX, V1 layout is used.
#[test]
fn keys_larger_than_u16_use_v1() {
    let mem = make_memory();
    let address = Address::from(0);
    let mut node = Node::<Vec<u8>>::new(address, NodeType::Leaf, u16::MAX as u32 + 1, 0);
    node.insert_entry(0, (vec![], vec![]));
    assert_eq!(node.version, Version::V1.into());

    // Save and reload. Version should still be V1.
    node.save(&mem);
    let node = Node::<Vec<u8>>::load(address, &mem, u16::MAX as u32 + 1, 0);
    assert_eq!(node.version, Version::V1.into());
}

// Verifies that, if the key is <= u16::MAX, V2 layout is used.
#[test]
fn keys_within_u16_use_v2() {
    let mem = make_memory();
    let address = Address::from(0);
    let mut node = Node::<Vec<u8>>::new(address, NodeType::Leaf, u16::MAX as u32, 0);
    node.insert_entry(0, (vec![], vec![]));
    assert_eq!(node.version, Version::V2.into());

    // Save and reload. Version should still be V1.
    node.save(&mem);
    let node = Node::<Vec<u8>>::load(address, &mem, u16::MAX as u32, 0);
    assert_eq!(node.version, Version::V2.into());
}
