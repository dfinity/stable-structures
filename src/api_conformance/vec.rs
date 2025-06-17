use crate::api_conformance::make_memory;
use crate::vec::Vec;

#[test]
fn api_conformance() {
    let mem = make_memory();
    let stable = Vec::new(mem).unwrap();
    let mut std = std::vec::Vec::new();
    let n = 10_u32;

    // Push elements.
    for i in 0..n {
        stable.push(&i).expect("push failed");
        std.push(i);
    }

    // Length and is_empty.
    // Note: stable.len() returns u64, std.len() returns usize.
    assert_eq!(stable.len(), std.len() as u64);
    assert_eq!(stable.is_empty(), std.is_empty());

    // Get by index.
    // Note: stable.get returns Option<&T>, std returns Option<&T>.
    for i in 0..n {
        assert_eq!(stable.get(i as u64), Some(std[i as usize]));
    }

    // Set by index.
    // Note: stable.set uses &T, std uses indexing.
    for i in 0..n {
        let value = i * 10;
        stable.set(i as u64, &value);
        std[i as usize] = value;
    }

    // Confirm updated values.
    for i in 0..n {
        assert_eq!(stable.get(i as u64), Some(std[i as usize]));
    }

    // TODO: add Copy trait to iter.
    // // Iteration.
    // // Note: stable.iter() yields &T, std.iter() yields &T.
    // let stable_items: Vec<_> = stable.iter().copied().collect();
    // let std_items: Vec<_> = std.iter().copied().collect();
    // assert_eq!(stable_items, std_items);

    // Pop elements.
    // Note: stable.pop() and std.pop() both return Option<T>.
    for _ in 0..n {
        assert_eq!(stable.pop(), std.pop());
    }

    // After popping everything, both should be empty.
    assert_eq!(stable.len(), std.len() as u64);
    assert_eq!(stable.is_empty(), std.is_empty());
}
