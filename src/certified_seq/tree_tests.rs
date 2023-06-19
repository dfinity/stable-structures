use super::*;

#[test]
fn test_left_parent() {
    for n in [0, 1, 3, 7] {
        assert_eq!(
            left_parent(n),
            None,
            "Node {} does not have a left parent",
            n
        )
    }
    for (n, p) in [
        (2, 1),
        (4, 3),
        (5, 3),
        (6, 5),
        (8, 7),
        (9, 7),
        (10, 9),
        (11, 7),
        (12, 11),
        (13, 11),
    ] {
        assert_eq!(
            left_parent(n),
            Some(p),
            "Expected the parent of node {} to be {}",
            n,
            p
        );
    }
}

#[test]
fn test_full_tree_right_child() {
    let answers = [
        None,
        Some(2),
        None,
        Some(5),
        None,
        Some(6),
        None,
        Some(11),
        None,
        Some(10),
        None,
        Some(13),
        None,
        Some(14),
        None,
    ];
    for (node, answer) in answers.into_iter().enumerate() {
        assert_eq!(
            full_tree_right_child(node as u64),
            answer,
            "Failed on node {node}"
        );
    }
}

#[test]
fn test_right_child() {
    assert_eq!(right_child(15, 19), Some(17));
    assert_eq!(right_child(11, 13), Some(12));
}

#[test]
fn test_left_child() {
    assert_eq!(left_child(0), None);
    assert_eq!(left_child(1), Some(0));
    assert_eq!(left_child(2), None);
    assert_eq!(left_child(3), Some(1));
    assert_eq!(left_child(5), Some(4));
    assert_eq!(left_child(7), Some(3));
    assert_eq!(left_child(9), Some(8));
    assert_eq!(left_child(11), Some(9));
    assert_eq!(left_child(13), Some(12));
    assert_eq!(left_child(15), Some(7));
}

#[test]
fn test_node_parent() {
    use NodeParent::*;
    let answers = [
        LeftChildOf(1),
        LeftChildOf(3),
        RightChildOf(1),
        LeftChildOf(7),
        LeftChildOf(5),
        RightChildOf(3),
        RightChildOf(5),
        Root,
        LeftChildOf(9),
        LeftChildOf(11),
        RightChildOf(9),
        RightChildOf(7),
        RightChildOf(11),
    ];
    for (node, answer) in answers.into_iter().enumerate() {
        assert_eq!(
            node_parent(node as u64, answers.len() as u64),
            answer,
            "Failed for node {node}"
        );
    }
}

#[test]
fn test_full_tree_is_left_child() {
    let table = [1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0];
    for (i, flag) in table.into_iter().enumerate() {
        assert_eq!(
            is_full_tree_left_child(i as u64),
            flag == 1,
            "Error for node {i}"
        );
    }
}

#[test]
fn test_tree_root() {
    assert_eq!(tree_root(0), None);
    assert_eq!(tree_root(1), Some(0));
    assert_eq!(tree_root(3), Some(1));
    assert_eq!(tree_root(5), Some(3));
    assert_eq!(tree_root(7), Some(3));
    assert_eq!(tree_root(9), Some(7));
    assert_eq!(tree_root(11), Some(7));
    assert_eq!(tree_root(13), Some(7));
}
