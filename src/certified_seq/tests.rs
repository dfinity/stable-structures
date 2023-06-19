use super::*;
use crate::certification::WitnessBuilder;
use crate::DefaultMemoryImpl;
use ic_agent::hash_tree::{self, HashTree};
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::collections::VecDeque;

fn compute_seq_hashes(leaves: &[Vec<u8>]) -> Vec<Hash> {
    enum Tree {
        Leaf(Hash),
        Fork(Hash, Box<Tree>, Box<Tree>),
    }

    impl Tree {
        fn hash(&self) -> &Hash {
            match self {
                Self::Leaf(h) => h,
                Self::Fork(h, _, _) => h,
            }
        }

        fn flatten(&self, sink: &mut Vec<Hash>) {
            match self {
                Self::Leaf(h) => sink.push(*h),
                Self::Fork(h, l, r) => {
                    l.flatten(sink);
                    sink.push(*h);
                    r.flatten(sink);
                }
            }
        }
    }

    let mut current: VecDeque<_> = leaves
        .iter()
        .enumerate()
        .map(|(i, bs)| Tree::Leaf(leaf_subtree_hash(i as u64, &leaf_hash(bs))))
        .collect();

    let mut last = VecDeque::new();

    while current.len() > 1 {
        std::mem::swap(&mut current, &mut last);
        while let Some(t1) = last.pop_front() {
            if let Some(t2) = last.pop_front() {
                current.push_back(Tree::Fork(
                    fork_hash(t1.hash(), t2.hash()),
                    Box::new(t1),
                    Box::new(t2),
                ));
            } else {
                current.push_back(t1);
            }
        }
    }

    let mut result = vec![];
    if let Some(t) = current.pop_front() {
        t.flatten(&mut result);
    }
    result
}

struct IcAgentTreeBuilder;
impl WitnessBuilder for IcAgentTreeBuilder {
    type Tree = HashTree<Vec<u8>>;

    fn empty() -> Self::Tree {
        hash_tree::empty()
    }

    fn fork(left: Self::Tree, right: Self::Tree) -> Self::Tree {
        hash_tree::fork(left, right)
    }

    fn node(label: &[u8], child: Self::Tree) -> Self::Tree {
        hash_tree::label(label, child)
    }

    fn leaf(data: &[u8]) -> Self::Tree {
        hash_tree::leaf(data)
    }

    fn pruned(hash: [u8; 32]) -> Self::Tree {
        hash_tree::pruned(hash)
    }
}

proptest! {
    #[test]
    fn test_inorder_node_hashes(data in pvec(pvec(any::<u8>(), 0..50), 1..32)) {
        let expected = compute_seq_hashes(&data);
        let seq = CertifiedSeq::new(DefaultMemoryImpl::default()).unwrap();
        for blob in &data {
            seq.append(blob).unwrap();
        }

        prop_assert_eq!(seq.0.len(), expected.len() as u64);

        for (i, h) in expected.iter().enumerate() {
            let i = i as u64;
            let hash = seq.0.get(i).unwrap();
            let actual = if i % 2 == 0 { leaf_subtree_hash(i / 2, &hash) } else { hash };
            prop_assert_eq!(
                actual, *h,
                "differ at index {}, expected sequence: {:?}", i, &expected
            );
        }
    }

    #[test]
    fn test_witness_generation(data in pvec(pvec(any::<u8>(), 0..50), 0..32)) {
        let seq = CertifiedSeq::new(DefaultMemoryImpl::default()).unwrap();
        for blob in &data {
            seq.append(blob).unwrap();
        }

        for (i, b) in data.iter().enumerate() {
            let tree = seq.witness_item::<IcAgentTreeBuilder>(i as u64, b);
            prop_assert_eq!(tree.digest(), seq.root_hash());
            prop_assert_eq!(tree.lookup_path(&[&i.to_be_bytes()]), hash_tree::LookupResult::Found(b));
        }
        let missing = data.len() as u64 + 1;
        let tree = seq.witness_item::<IcAgentTreeBuilder>(missing, b"");
        prop_assert_eq!(tree.lookup_path(&[&missing.to_be_bytes()]), hash_tree::LookupResult::Absent);
    }
}
