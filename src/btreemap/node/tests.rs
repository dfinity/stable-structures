use super::*;
use crate::{btreemap::allocator::Allocator, types::NULL};
use proptest::collection::btree_map as pmap;
use proptest::collection::vec as pvec;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;
use test_strategy::{proptest, Arbitrary};

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

#[derive(Arbitrary, Debug)]
struct NodeV1Data {
    #[strategy(1..100u32)]
    max_key_size: u32,
    #[strategy(1..1_000u32)]
    max_value_size: u32,

    // NOTE: A BTreeMap is used for creating the entries so that they'd be in sorted order.
    #[strategy(
        pmap(
            pvec(0..u8::MAX, 0..#max_key_size as usize),
            pvec(0..u8::MAX, 0..#max_value_size as usize),
            1..CAPACITY
        )
    )]
    entries: BTreeMap<Vec<u8>, Vec<u8>>,
    node_type: NodeType,
}

impl NodeV1Data {
    fn get(&self, address: Address) -> Node<Vec<u8>> {
        // Create a new node.
        let mut node = Node::new_v1(
            address,
            self.node_type,
            self.max_key_size,
            self.max_value_size,
        );

        for entry in self.entries.clone().into_iter() {
            node.push_entry(entry);
        }

        // If the node is an internal node, then insert some children addresses.
        if self.node_type == NodeType::Internal {
            for i in 0..=self.entries.len() {
                node.push_child(Address::from(i as u64));
            }
        }
        node
    }

    fn children(&self) -> Vec<Address> {
        if self.node_type == NodeType::Internal {
            (0..=self.entries.len())
                .map(|i| Address::from(i as u64))
                .collect()
        } else {
            vec![]
        }
    }
}

#[derive(Arbitrary, Debug)]
struct NodeV2Data {
    // FIXME: figure out proper lower bound for page size.
    #[strategy(15..2_000_u32)]
    page_size: u32,
    #[strategy(
        pmap(
            pvec(0..u8::MAX, 0..100),
            pvec(0..u8::MAX, 0..100),
            1..CAPACITY
        )
    )]
    entries: BTreeMap<Vec<u8>, Vec<u8>>,
    node_type: NodeType,
}

impl NodeV2Data {
    fn get(&self, address: Address) -> Node<Vec<u8>> {
        let mut node = Node::new_v2(address, self.node_type, PageSize::Absolute(self.page_size));
        for entry in self.entries.clone().into_iter() {
            node.push_entry(entry);
        }
        // If the node is an internal node, then insert some children addresses.
        if self.node_type == NodeType::Internal {
            for i in 0..=self.entries.len() {
                node.push_child(Address::from(i as u64));
            }
        }
        node
    }

    fn children(&self) -> Vec<Address> {
        if self.node_type == NodeType::Internal {
            (0..=self.entries.len())
                .map(|i| Address::from(i as u64))
                .collect()
        } else {
            vec![]
        }
    }
}

// Validates that saving and loading a V1 node preserves all the data.
#[proptest]
fn saving_and_loading_v1(node_data: NodeV1Data) {
    let mem = make_memory();

    // Create a new node and save it into memory.
    let node = node_data.get(NULL);
    node.save_v1(&mem);

    // Reload the node and double check all the entries and children are correct.
    let node = Node::load_v1(
        NULL,
        Version::V1 {
            max_key_size: node_data.max_key_size,
            max_value_size: node_data.max_value_size,
        },
        &mem,
    );

    assert_eq!(node.children, node_data.children());
    assert_eq!(
        node.entries(&mem),
        node_data.entries.into_iter().collect::<Vec<_>>()
    );
}

#[proptest]
fn saving_and_loading_v2(node_data: NodeV2Data) {
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let mut allocator = Allocator::new(
        mem.clone(),
        allocator_addr,
        Bytes::from(node_data.page_size as u64),
    );

    // Create a new node and save it into memory.
    let node_addr = allocator.allocate();
    let node = node_data.get(node_addr);
    node.save_v2(&mut allocator);

    // Reload the node and double check all the entries and children are correct.
    let node = Node::load_v2(node_addr, PageSize::Absolute(node_data.page_size), &mem);

    assert_eq!(node.children, node_data.children());
    assert_eq!(
        node.entries(&mem),
        node_data.entries.into_iter().collect::<Vec<_>>()
    );
}

#[proptest]
fn migrating_v1_nodes_to_v2(node_data: NodeV1Data) {
    let v1_size = v1::size_v1(node_data.max_key_size, node_data.max_value_size);
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let mut allocator = Allocator::new(mem.clone(), allocator_addr, v1_size);

    // Create a v1 node and save it into memory as v1.
    let node_addr = allocator.allocate();
    let node = node_data.get(node_addr);
    node.save_v1(allocator.memory());

    // Reload the v1 node and save it as v2.
    let node = Node::<Vec<u8>>::load_v1(
        node_addr,
        Version::V1 {
            max_key_size: node_data.max_key_size,
            max_value_size: node_data.max_value_size,
        },
        allocator.memory(),
    );
    node.save_v2(&mut allocator);

    // Reload the now v2 node and double check all the entries and children are correct.
    let node = Node::load_v2(
        node_addr,
        PageSize::Kv(node_data.max_key_size, node_data.max_value_size),
        &mem,
    );

    assert_eq!(node.children, node_data.children());
    assert_eq!(
        node.entries(&mem),
        node_data.entries.into_iter().collect::<Vec<_>>()
    );
}
