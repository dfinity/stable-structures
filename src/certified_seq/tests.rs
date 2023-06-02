use super::*;
use crate::DefaultMemoryImpl;
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
        .map(|(i, bs)| Tree::Leaf(leaf_hash(i as u64, bs)))
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
            prop_assert_eq!(
                seq.0.get(i as u64).unwrap(), *h,
                "differ at index {}, expected sequence: {:?}", i, &expected
            );
        }
    }
}
