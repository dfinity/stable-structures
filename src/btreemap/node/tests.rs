use super::*;
use crate::types::NULL;
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
fn loading_and_reloading_entries(
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
    let mut node = Node::new(NULL, NodeType::Leaf, max_key_size, max_value_size);
    for entry in entries.clone().into_iter() {
        node.push_entry(entry);
    }
    node.save(&mem);

    // Reload the node and double check all the entries are correct.
    let node = Node::load(NULL, &mem, max_key_size, max_value_size);
    assert_eq!(node.entries(&mem), entries.into_iter().collect::<Vec<_>>());
}
