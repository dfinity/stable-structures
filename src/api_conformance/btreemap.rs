use crate::api_conformance::make_memory;
use crate::btreemap::BTreeMap;

#[test]
fn api_conformance() {
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
    let stable_items: Vec<_> = stable.iter().collect();
    let std_items: Vec<_> = std.iter().map(|(k, v)| (*k, v.clone())).collect();
    assert_eq!(stable_items, std_items);

    let stable_keys: Vec<_> = stable.keys().collect();
    let std_keys: Vec<_> = std.keys().copied().collect();
    assert_eq!(stable_keys, std_keys);

    let stable_values: Vec<_> = stable.values().collect();
    let std_values: Vec<_> = std.values().cloned().collect();
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

    let stable_range: Vec<_> = stable.range(range_start..range_end).collect();
    let std_range: Vec<_> = std
        .range(range_start..range_end)
        .map(|(k, v)| (*k, v.clone()))
        .collect();
    assert_eq!(stable_range, std_range);

    // keys_range
    // Note: stable has a dedicated keys_range() method; std uses map.range().map(|(k, _)| ...)
    let stable_keys_range: Vec<_> = stable.keys_range(range_start..range_end).collect();
    let std_keys_range: Vec<_> = std.range(range_start..range_end).map(|(k, _)| *k).collect();
    assert_eq!(stable_keys_range, std_keys_range);

    // values_range
    // Note: stable has a dedicated values_range() method; std uses map.range().map(|(_, v)| ...)
    let stable_values_range: Vec<_> = stable.values_range(range_start..range_end).collect();
    let std_values_range: Vec<_> = std
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
    let stable_result: Vec<_> = stable.iter_from_prev_key(&bound).collect();
    let std_result: Vec<_> = if let Some((start, _)) = std.range(..bound).next_back() {
        std.range(start..).map(|(k, v)| (*k, v.clone())).collect()
    } else {
        Vec::new()
    };
    assert_eq!(stable_result, std_result);
}
