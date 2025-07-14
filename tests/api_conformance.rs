use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::rc::Rc;

use ic_stable_structures::btreemap::BTreeMap;
use ic_stable_structures::btreeset::BTreeSet;
use ic_stable_structures::cell::Cell as StableCell;
use ic_stable_structures::log::Log as StableLog;
use ic_stable_structures::min_heap::MinHeap;
use ic_stable_structures::vec::Vec as StableVec;

pub fn make_memory() -> Rc<RefCell<std::vec::Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

#[test]
fn api_conformance_btreemap() {
    let mem = make_memory();
    let mut stable = BTreeMap::new(mem);
    let mut std = std::collections::BTreeMap::new();
    let n = 10_u32;

    // Insert keys and values.
    for i in 0..n {
        stable.insert(i, format!("{i}"));
        std.insert(i, format!("{i}"));
    }

    // Get and contains.
    // Note: stable.get returns owned value (Option<V>), std.get returns reference (Option<&V>).
    assert_eq!(stable.get(&1), std.get(&1).cloned());
    assert_eq!(stable.contains_key(&1), std.contains_key(&1));

    // Remove.
    // Same return behavior as get: stable returns owned value, std returns owned too.
    assert_eq!(stable.remove(&1), std.remove(&1));

    // Length and is_empty.
    // Note: stable.len() returns u64, std.len() returns usize.
    assert_eq!(stable.len(), std.len() as u64);
    assert_eq!(stable.is_empty(), std.is_empty());

    // Clear.
    // Note: stable uses clear_new(); std uses clear().
    stable.clear_new();
    std.clear();
    assert_eq!(stable.len(), std.len() as u64);
    assert_eq!(stable.is_empty(), std.is_empty());

    // Re-insert to test iteration-related methods.
    for i in 0..n {
        let v = i.to_string();
        stable.insert(i, v.clone());
        std.insert(i, v);
    }

    // Iterators.
    // Note: stable.iter() yields (K, V), std.iter() yields (&K, &V)
    let stable_items: std::vec::Vec<_> = stable.iter().collect();
    let std_items: std::vec::Vec<_> = std.iter().map(|(k, v)| (*k, v.clone())).collect();
    assert_eq!(stable_items, std_items);

    let stable_keys: std::vec::Vec<_> = stable.keys().collect();
    let std_keys: std::vec::Vec<_> = std.keys().copied().collect();
    assert_eq!(stable_keys, std_keys);

    let stable_values: std::vec::Vec<_> = stable.values().collect();
    let std_values: std::vec::Vec<_> = std.values().cloned().collect();
    assert_eq!(stable_values, std_values);

    // First and last.
    // Note: stable returns (K, V), std returns (&K, &V)
    let stable_first = stable.first_key_value();
    let std_first = std.first_key_value().map(|(k, v)| (*k, v.clone()));
    assert_eq!(stable_first, std_first);

    let stable_last = stable.last_key_value();
    let std_last = std.last_key_value().map(|(k, v)| (*k, v.clone()));
    assert_eq!(stable_last, std_last);

    // Pop first and last.
    // Note: both stable and std return Option<(K, V)>
    let stable_pop_first = stable.pop_first();
    let std_pop_first = std.pop_first();
    assert_eq!(stable_pop_first, std_pop_first);

    let stable_pop_last = stable.pop_last();
    let std_pop_last = std.pop_last();
    assert_eq!(stable_pop_last, std_pop_last);

    // Range.
    let range_start = 3;
    let range_end = 7;

    let stable_range: std::vec::Vec<_> = stable.range(range_start..range_end).collect();
    let std_range: std::vec::Vec<_> = std
        .range(range_start..range_end)
        .map(|(k, v)| (*k, v.clone()))
        .collect();
    assert_eq!(stable_range, std_range);

    // keys_range
    // Note: stable has a dedicated keys_range() method; std uses map.range().map(|(k, _)| ...)
    let stable_keys_range: std::vec::Vec<_> = stable.keys_range(range_start..range_end).collect();
    let std_keys_range: std::vec::Vec<_> =
        std.range(range_start..range_end).map(|(k, _)| *k).collect();
    assert_eq!(stable_keys_range, std_keys_range);

    // values_range
    // Note: stable has a dedicated values_range() method; std uses map.range().map(|(_, v)| ...)
    let stable_values_range: std::vec::Vec<_> =
        stable.values_range(range_start..range_end).collect();
    let std_values_range: std::vec::Vec<_> = std
        .range(range_start..range_end)
        .map(|(_, v)| v.clone())
        .collect();
    assert_eq!(stable_values_range, std_values_range);

    // iter_from_prev_key
    // Note: stable.iter_from_prev_key(bound) is a custom method.
    // It starts from the largest key strictly less than `bound`, and continues forward.
    // To simulate in std: use .range(..bound).next_back() to get the largest < bound,
    // then iterate from that key forward using .range(start..).
    let bound = 5;
    let stable_result: std::vec::Vec<_> = stable.iter_from_prev_key(&bound).collect();
    let std_result: std::vec::Vec<_> = if let Some((start, _)) = std.range(..bound).next_back() {
        std.range(start..).map(|(k, v)| (*k, v.clone())).collect()
    } else {
        Vec::new()
    };
    assert_eq!(stable_result, std_result);
}

#[test]
fn api_conformance_btreeset() {
    let mem = make_memory();
    let mut stable = BTreeSet::new(mem);
    let mut std = std::collections::BTreeSet::new();
    let n = 10_u32;

    // Insert elements.
    for i in 0..n {
        assert_eq!(stable.insert(i), std.insert(i));
    }

    // Contains.
    for i in 0..n {
        assert_eq!(stable.contains(&i), std.contains(&i));
    }

    // is_empty and len.
    // Note: stable.len() returns u64, std.len() returns usize.
    assert_eq!(stable.is_empty(), std.is_empty());
    assert_eq!(stable.len(), std.len() as u64);

    // First and last.
    // Note: stable.first()/last() returns Option<T>, std returns Option<&T>.
    assert_eq!(stable.first(), std.first().copied());
    assert_eq!(stable.last(), std.last().copied());

    // Iteration.
    // Note: stable.iter() yields T, std.iter() yields &T.
    let stable_items: std::vec::Vec<_> = stable.iter().collect();
    let std_items: std::vec::Vec<_> = std.iter().copied().collect();
    assert_eq!(stable_items, std_items);

    // Range.
    let range_start = 3;
    let range_end = 7;
    let stable_range: std::vec::Vec<_> = stable.range(range_start..range_end).collect();
    let std_range: std::vec::Vec<_> = std.range(range_start..range_end).copied().collect();
    assert_eq!(stable_range, std_range);

    // pop_first / pop_last.
    let mem2 = make_memory();
    let mut stable_temp = BTreeSet::new(mem2);
    let mut std_temp = std::collections::BTreeSet::new();
    for i in 0..n {
        assert_eq!(stable_temp.insert(i), std_temp.insert(i));
    }

    assert_eq!(stable_temp.pop_first(), std_temp.pop_first());
    assert_eq!(stable_temp.pop_last(), std_temp.pop_last());

    // Remove elements.
    for i in 0..n {
        assert_eq!(stable.remove(&i), std.remove(&i));
    }
    assert!(stable.is_empty());
    assert!(std.is_empty());

    // Clear.
    for i in 0..n {
        stable.insert(i);
        std.insert(i);
    }
    stable.clear();
    std.clear();
    assert!(stable.is_empty());
    assert!(std.is_empty());

    // Reinsert for set operations.
    for i in 0..n {
        if i % 2 == 0 {
            stable.insert(i);
            std.insert(i);
        }
    }

    let mem2 = make_memory();
    let mut stable2 = BTreeSet::new(mem2);
    let mut std2 = std::collections::BTreeSet::new();

    for i in 0..n {
        if i % 3 == 0 {
            stable2.insert(i);
            std2.insert(i);
        }
    }

    // is_disjoint, is_subset, is_superset.
    assert_eq!(stable.is_disjoint(&stable2), std.is_disjoint(&std2));
    assert_eq!(stable.is_subset(&stable2), std.is_subset(&std2));
    assert_eq!(stable.is_superset(&stable2), std.is_superset(&std2));

    // union
    let stable_union: std::vec::Vec<_> = stable.union(&stable2).collect();
    let std_union: std::vec::Vec<_> = std.union(&std2).copied().collect();
    assert_eq!(stable_union, std_union);

    // intersection
    let stable_inter: std::vec::Vec<_> = stable.intersection(&stable2).collect();
    let std_inter: std::vec::Vec<_> = std.intersection(&std2).copied().collect();
    assert_eq!(stable_inter, std_inter);

    // symmetric_difference
    let stable_diff: std::vec::Vec<_> = stable.symmetric_difference(&stable2).collect();
    let std_diff: std::vec::Vec<_> = std.symmetric_difference(&std2).copied().collect();
    assert_eq!(stable_diff, std_diff);
}

#[test]
fn api_conformance_min_heap() {
    let mem = make_memory();
    let mut stable = MinHeap::new(mem);
    let mut std = BinaryHeap::new();
    let n = 10_u32;

    // Push elements.
    for i in 0..n {
        stable.push(&i);
        std.push(Reverse(i));
    }

    // Length and is_empty.
    // Note: stable.len() returns u64, std.len() returns usize.
    assert_eq!(stable.len(), std.len() as u64);
    assert_eq!(stable.is_empty(), std.is_empty());

    // Peek (min element).
    // Note: stable.peek() returns Option<T>, std.peek() returns Option<&Reverse<T>>.
    assert_eq!(stable.peek(), std.peek().map(|r| r.0));

    // Pop all elements, should match in ascending order.
    let mut stable_popped = Vec::new();
    let mut std_popped = Vec::new();
    while let Some(v) = stable.pop() {
        stable_popped.push(v);
    }
    while let Some(Reverse(v)) = std.pop() {
        std_popped.push(v);
    }
    assert_eq!(stable_popped, std_popped);

    // After popping everything, both should be empty.
    assert_eq!(stable.len(), 0);
    assert!(stable.is_empty());
    assert!(std.is_empty());
}

#[test]
fn api_conformance_vec() {
    let mem = make_memory();
    let stable = StableVec::new(mem);
    let mut std = Vec::new();
    let n = 10_u32;

    // Push elements.
    for i in 0..n {
        stable.push(&i);
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

    // Pop elements.
    // Note: stable.pop() and std.pop() both return Option<T>.
    for _ in 0..n {
        assert_eq!(stable.pop(), std.pop());
    }

    // After popping everything, both should be empty.
    assert_eq!(stable.len(), std.len() as u64);
    assert_eq!(stable.is_empty(), std.is_empty());
}

#[test]
fn api_conformance_cell() {
    let mem = make_memory();

    // use u32 for simplicity; also supported by Storable
    let initial = 42u32;
    let updated = 777u32;

    let mut stable = StableCell::new(mem.clone(), initial);
    let std = RefCell::new(initial);

    // Get
    assert_eq!(*stable.get(), *std.borrow());

    // Set
    let old_stable = stable.set(updated);
    let old_std = std.replace(updated);
    assert_eq!(old_stable, old_std);

    // After set
    assert_eq!(*stable.get(), *std.borrow());

    // Check that the value persists across re-init
    let stable = StableCell::init(mem, 0);
    assert_eq!(*stable.get(), updated);
}

#[test]
fn api_conformance_log() {
    let index_mem = make_memory();
    let data_mem = make_memory();
    let log = StableLog::new(index_mem.clone(), data_mem.clone());
    let mut std = Vec::new();

    let n = 10_u32;

    // Append elements and compare returned indices
    for i in 0..n {
        let idx = log.append(&i).expect("append should succeed");
        assert_eq!(idx, std.len() as u64);
        std.push(i);
    }

    // Length and is_empty
    assert_eq!(log.len(), std.len() as u64);
    assert_eq!(log.is_empty(), std.is_empty());

    // Get by index
    for i in 0..n {
        assert_eq!(log.get(i as u64), Some(std[i as usize]));
    }

    // Iteration
    let log_items: Vec<_> = log.iter().collect();
    assert_eq!(log_items, std);
}
