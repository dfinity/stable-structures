use super::*;
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
            self.max_key_size,
            self.max_value_size,
        );

        // Push the entries
        for entry in self.entries.clone().into_iter() {
            node.push_entry(entry);
        }

        // Push the chilren
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
    let node = Node::load_v1(
        node_addr,
        node_data.max_key_size,
        node_data.max_value_size,
        &mem,
    );

    assert_eq!(node.children, node_data.children());
    assert_eq!(
        node.entries(&mem),
        node_data.entries.into_iter().collect::<Vec<_>>()
    );
}
