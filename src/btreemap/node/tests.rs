use crate::btreemap::{node::{CAPACITY, Version}, Node, NodeType};
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
        assert_eq!(node.version, Version::V1);

        // Saving the node with the v2 layout should also work and preserve the entries.
        node.save_v2(&mem);
        let node = Node::<Vec<u8>>::load(Address::from(0), &mem, 10, 10);
        assert_eq!(node.entries(&mem), entries);
        assert_eq!(node.version, Version::V2);
    });
}
