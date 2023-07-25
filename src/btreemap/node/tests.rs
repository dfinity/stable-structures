use super::*;
use crate::{btreemap::allocator::Allocator, types::NULL};
use proptest::collection::btree_map as pmap;
use proptest::collection::vec as pvec;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;
use test_strategy::proptest;

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

#[proptest]
fn loading_and_reloading_entries_v1(
    #[strategy(1..100u32)] max_key_size: u32,
    #[strategy(1..1_000u32)] max_value_size: u32,
    #[strategy(
        pmap(
            pvec(0..u8::MAX, 0..#max_key_size as usize),
            pvec(0..u8::MAX, 0..#max_value_size as usize),
            1..CAPACITY
        )
    )]
    entries: BTreeMap<Vec<u8>, Vec<u8>>,
) {
    let mem = make_memory();

    // Create a new node and save it into memory.
    let mut node = Node::new_v1(NULL, NodeType::Leaf, max_key_size, max_value_size);
    for entry in entries.clone().into_iter() {
        node.push_entry(entry);
    }
    node.save_v1(&mem);

    // Reload the node and double check all the entries are correct.
    let node = Node::load_v1(
        NULL,
        Version::V1 {
            max_key_size,
            max_value_size,
        },
        &mem,
    );
    assert_eq!(node.entries(&mem), entries.into_iter().collect::<Vec<_>>());
}

#[proptest]
fn loading_and_reloading_entries_v2(
    #[strategy(12..2_000_u32)] page_size: u32,
    #[strategy(
        pmap(
            pvec(0..u8::MAX, 0..100),
            pvec(0..u8::MAX, 0..100),
            1..CAPACITY
        )
    )]
    entries: BTreeMap<Vec<u8>, Vec<u8>>,
) {
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let mut allocator = Allocator::new(mem.clone(), allocator_addr, Bytes::from(page_size as u64));

    // Create a new node and save it into memory.
    let node_addr = allocator.allocate();
    let mut node = Node::new_v2(node_addr, NodeType::Leaf, page_size);
    for entry in entries.clone().into_iter() {
        node.push_entry(entry);
    }
    node.save_v2(&mut allocator);

    // Reload the node and double check all the entries are correct.
    let node = Node::load_v2(node_addr, Version::V2(PageSize::Absolute(page_size)), &mem);
    assert_eq!(node.entries(&mem), entries.into_iter().collect::<Vec<_>>());
}

#[proptest]
fn migrating_v1_nodes_to_v2(
    #[strategy(1..100u32)] max_key_size: u32,
    #[strategy(1..1_000u32)] max_value_size: u32,
    #[strategy(
        pmap(
            pvec(0..u8::MAX, 0..#max_key_size as usize),
            pvec(0..u8::MAX, 0..#max_value_size as usize),
            1..CAPACITY
        )
    )]
    entries: BTreeMap<Vec<u8>, Vec<u8>>,
) {
    let v1_size = v1::size_v1(max_key_size, max_value_size);
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let mut allocator = Allocator::new(mem.clone(), allocator_addr, v1_size);

    // Create a v1 node and save it into memory as v1.
    let node_addr = allocator.allocate();
    let mut node = Node::new_v1(node_addr, NodeType::Leaf, max_key_size, max_value_size);
    for entry in entries.clone().into_iter() {
        node.push_entry(entry);
    }
    node.save_v1(allocator.memory());

    // Reload the v1 node and save it as v2.
    let node = Node::<Vec<u8>>::load_v1(
        node_addr,
        Version::V1 {
            max_key_size,
            max_value_size,
        },
        allocator.memory(),
    );
    node.save_v2(&mut allocator);

    // Reload the now v2 node and double check all the entries are correct.
    let node = Node::load_v2(
        node_addr,
        Version::V2(PageSize::Kv(max_key_size, max_value_size)),
        &mem,
    );
    assert_eq!(node.entries(&mem), entries.into_iter().collect::<Vec<_>>());
}
