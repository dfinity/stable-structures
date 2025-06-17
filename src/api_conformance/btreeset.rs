use crate::api_conformance::make_memory;
use crate::btreeset::BTreeSet;

#[test]
fn api_conformance() {
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
    let stable_items: Vec<_> = stable.iter().collect();
    let std_items: Vec<_> = std.iter().copied().collect();
    assert_eq!(stable_items, std_items);

    // Range.
    let range_start = 3;
    let range_end = 7;
    let stable_range: Vec<_> = stable.range(range_start..range_end).collect();
    let std_range: Vec<_> = std.range(range_start..range_end).copied().collect();
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
    let stable_union: Vec<_> = stable.union(&stable2).collect();
    let std_union: Vec<_> = std.union(&std2).copied().collect();
    assert_eq!(stable_union, std_union);

    // intersection
    let stable_inter: Vec<_> = stable.intersection(&stable2).collect();
    let std_inter: Vec<_> = std.intersection(&std2).copied().collect();
    assert_eq!(stable_inter, std_inter);

    // symmetric_difference
    let stable_diff: Vec<_> = stable.symmetric_difference(&stable2).collect();
    let std_diff: Vec<_> = std.symmetric_difference(&std2).copied().collect();
    assert_eq!(stable_diff, std_diff);
}
