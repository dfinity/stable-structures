use super::*;
use crate::{
    btreemap::{
        node::v2::{OVERFLOW_ADDRESS_OFFSET, PAGE_OVERFLOW_NEXT_OFFSET},
        Allocator,
    },
    types::NULL,
};
use proptest::collection::btree_map as pmap;
use proptest::collection::vec as pvec;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;
use test_strategy::{proptest, Arbitrary};

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

/// Generates arbitrary v1 nodes.
#[derive(Arbitrary, Debug)]
struct NodeV1Data {
    #[strategy(0..1_000u32)]
    max_key_size: u32,
    #[strategy(0..1_000u32)]
    max_value_size: u32,

    // NOTE: A BTreeMap is used for creating the entries so that they're in sorted order.
    #[strategy(
        pmap(
            pvec(0..u8::MAX, 0..=#max_key_size as usize),
            pvec(0..u8::MAX, 0..=#max_value_size as usize),
            1..CAPACITY
        )
    )]
    entries: BTreeMap<Vec<u8>, Vec<u8>>,
    node_type: NodeType,
}

impl NodeV1Data {
    /// Returns a v1 node with the data generated by this struct.
    fn get(&self, address: Address) -> Node<Vec<u8>> {
        let mut node = Node::new_v1(
            address,
            self.node_type,
            DerivedPageSize {
                max_key_size: self.max_key_size,
                max_value_size: self.max_value_size,
            },
        );

        // Push the entries
        for entry in self.entries.clone().into_iter() {
            node.push_entry(entry);
        }

        // Push the children
        for child in self.children() {
            node.push_child(child);
        }

        node
    }

    fn children(&self) -> Vec<Address> {
        match self.node_type {
            // A leaf node doesn't have any children.
            NodeType::Leaf => vec![],
            // An internal node has entries.len() + 1 children.
            // Here we generate a list of addresses.
            NodeType::Internal => (0..=self.entries.len())
                .map(|i| Address::from(i as u64))
                .collect(),
        }
    }
}

#[derive(Arbitrary, Debug)]
struct NodeV2Data {
    #[strategy(128..10_000_u32)]
    page_size: u32,
    #[strategy(
        pmap(
            pvec(0..u8::MAX, 0..1000),
            pvec(0..u8::MAX, 0..1000),
            1..CAPACITY
        )
    )]
    entries: BTreeMap<Vec<u8>, Vec<u8>>,
    node_type: NodeType,
}

impl NodeV2Data {
    fn get(&self, address: Address) -> Node<Vec<u8>> {
        let mut node = Node::new_v2(address, self.node_type, PageSize::Value(self.page_size));
        for entry in self.entries.clone().into_iter() {
            node.push_entry(entry);
        }
        for child in self.children() {
            node.push_child(child);
        }

        node
    }

    fn children(&self) -> Vec<Address> {
        match self.node_type {
            // A leaf node doesn't have any children.
            NodeType::Leaf => vec![],
            // An internal node has entries.len() + 1 children.
            // Here we generate a list of addresses.
            NodeType::Internal => (0..=self.entries.len())
                .map(|i| Address::from(i as u64))
                .collect(),
        }
    }
}

#[proptest]
fn saving_and_loading_v1_preserves_data(node_data: NodeV1Data) {
    let mem = make_memory();

    // Create a new node and save it into memory.
    let node_addr = Address::from(0);
    let node = node_data.get(node_addr);
    node.save_v1(&mem);

    // Load the node and double check all the entries and children are correct.
    let node = Node::load(
        node_addr,
        PageSize::Derived(DerivedPageSize {
            max_key_size: node_data.max_key_size,
            max_value_size: node_data.max_value_size,
        }),
        &mem,
    );

    assert_eq!(node.children, node_data.children());
    assert_eq!(
        node.entries(&mem),
        node_data.entries.into_iter().collect::<Vec<_>>()
    );
}

#[proptest]
fn saving_and_loading_v2_preserves_data(node_data: NodeV2Data) {
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let mut allocator = Allocator::new(
        mem.clone(),
        allocator_addr,
        Bytes::from(node_data.page_size as u64),
    );

    // Create a new node and save it into memory.
    let node_addr = allocator.allocate();
    let mut node = node_data.get(node_addr);
    node.save_v2(&mut allocator);

    // Reload the node and double check all the entries and children are correct.
    let node = Node::load(node_addr, PageSize::Value(node_data.page_size), &mem);

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
    let mut node = Node::<Vec<u8>>::load(
        node_addr,
        PageSize::Derived(DerivedPageSize {
            max_key_size: node_data.max_key_size,
            max_value_size: node_data.max_value_size,
        }),
        allocator.memory(),
    );
    node.save_v2(&mut allocator);

    // Reload the now v2 node and double check all the entries and children are correct.
    let node = Node::load(
        node_addr,
        PageSize::Derived(DerivedPageSize {
            max_key_size: node_data.max_key_size,
            max_value_size: node_data.max_value_size,
        }),
        &mem,
    );

    assert_eq!(node.children, node_data.children());
    assert_eq!(
        node.entries(&mem),
        node_data.entries.into_iter().collect::<Vec<_>>()
    );
}

#[test]
fn growing_and_shrinking_entries_does_not_leak_memory() {
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let mut allocator = Allocator::new(mem, allocator_addr, PageSize::Value(500).get().into());

    let mut node = Node::new_v2(allocator.allocate(), NodeType::Leaf, PageSize::Value(500));

    // Insert an entry substantially larger than the page size and save it.
    node.push_entry((vec![1, 2, 3], vec![0; 10000]));
    node.save(&mut allocator);

    let num_allocated_chunks = allocator.num_allocated_chunks();

    // The node is more than one page.
    assert!(num_allocated_chunks > 1);

    // Swap the value with a different one that is equal in length.
    node.swap_entry(0, (vec![1, 2, 3], vec![1; 10000]), allocator.memory());
    node.save(&mut allocator);

    // The number of allocated chunks hasn't changed.
    assert_eq!(num_allocated_chunks, allocator.num_allocated_chunks());

    // Swap the value with a much longer value.
    node.swap_entry(0, (vec![1, 2, 3], vec![2; 20000]), allocator.memory());
    node.save(&mut allocator);
    // More chunks are allocated to accommodate the longer value.
    assert!(num_allocated_chunks < allocator.num_allocated_chunks());

    // Swap the value with one that is similar in size to the original value.
    node.swap_entry(0, (vec![1, 2, 3], vec![3; 10000]), allocator.memory());
    node.save(&mut allocator);
    // The extra chunks are deallocated and we're back to the original number of chunks.
    assert_eq!(num_allocated_chunks, allocator.num_allocated_chunks());
}

#[test]
fn overflows_end_with_null_after_nodes_growing_and_shrinking() {
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let page_size = PageSize::Value(500);
    let mut allocator = Allocator::new(mem.clone(), allocator_addr, page_size.get().into());

    let node_addr = allocator.allocate();
    let mut node = Node::new_v2(node_addr, NodeType::Leaf, page_size);

    // Insert an entry larger than the page size and save it.
    node.push_entry((vec![1, 2, 3], vec![13; 1000]));
    node.save(&mut allocator);

    // Expect two overflow pages.
    assert_eq!(node.overflows().len(), 2);

    // The last overflow page should point to NULL.
    assert_eq!(
        read_u64(&mem, node.overflows()[1] + PAGE_OVERFLOW_NEXT_OFFSET),
        NULL.get()
    );

    // Replace the entry with a smaller value such that only one overflow page is needed.
    node.swap_entry(0, (vec![1, 2, 3], vec![7; 500]), allocator.memory());
    node.save(&mut allocator);

    // Expect one overflow page.
    assert_eq!(node.overflows().len(), 1);

    // The last overflow page should point to NULL.
    assert_eq!(
        read_u64(&mem, node.overflows()[0] + PAGE_OVERFLOW_NEXT_OFFSET),
        NULL.get()
    );

    // Replace the entry with a smaller value such that no overflow pages are needed.
    node.swap_entry(0, (vec![1, 2, 3], vec![]), allocator.memory());
    node.save(&mut allocator);

    // Expect no overflow pages.
    assert_eq!(node.overflows().len(), 0);

    // The initial page should point to NULL as it's overflow page.
    assert_eq!(
        read_u64(&mem, node_addr + OVERFLOW_ADDRESS_OFFSET),
        NULL.get()
    );
}

#[test]
fn can_call_node_value_multiple_times_on_same_index() {
    let mem = make_memory();
    let allocator_addr = Address::from(0);
    let page_size = PageSize::Value(500);
    let mut allocator = Allocator::new(mem.clone(), allocator_addr, page_size.get().into());

    let node_addr = allocator.allocate();
    let mut node = Node::new_v2(node_addr, NodeType::Leaf, page_size);
    node.push_entry((1u32, vec![1, 2, 3]));

    let value1 = node.value(0, &mem);
    let value2 = node.value(0, &mem);
    assert_eq!(&value1[..], &value2[..]);
}
