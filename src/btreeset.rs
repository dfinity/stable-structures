//! This module implements a set based on a B-Tree in stable memory.

use crate::{btreemap::Iter as IterMap, BTreeMap, Memory, Storable};
use core::ops::RangeBounds;

#[cfg(test)]
mod proptests;

/// An iterator over the entries of a [`BTreeSet`].
pub struct Iter<'a, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    iter_internal: IterMap<'a, K, (), M>,
}

impl<'a, K, M> Iter<'a, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    fn new(iter: IterMap<'a, K, (), M>) -> Self {
        Iter {
            iter_internal: iter,
        }
    }
}

impl<K, M> Iterator for Iter<'_, K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_internal.next().map(|entry| entry.key().clone())
    }
}

/// A B-Tree set implementation that stores its data into a designated memory.
///
/// # Overview
///
/// A `BTreeSet` is a "stable" set implementation based on a B-tree, designed to work directly in stable memory.
///
/// # Memory Implementations
///
/// `BTreeSet` works with any memory implementation that satisfies the [`Memory`] trait:
///
/// - [`Ic0StableMemory`](crate::Ic0StableMemory): Stores data in the Internet Computer's stable memory.
/// - [`VectorMemory`](crate::VectorMemory): In-memory implementation backed by a Rust `Vec<u8>`.
/// - [`FileMemory`](crate::FileMemory): Persists data to disk using a file.
/// - [`DefaultMemoryImpl`](crate::DefaultMemoryImpl): Automatically selects the appropriate memory backend
///   based on the environment:
///   - Uses `Ic0StableMemory` when running in an Internet Computer canister (wasm32 target).
///   - Falls back to `VectorMemory` in other environments (like tests or non-IC contexts).
///
/// For most use cases, [`DefaultMemoryImpl`](crate::DefaultMemoryImpl) is recommended as it provides
/// the right implementation based on the runtime context.
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust
/// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
/// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
///
/// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
/// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
///
/// set.insert(42);
/// assert!(set.contains(&42));
/// assert_eq!(set.pop_first(), Some(42));
/// assert!(set.is_empty());
/// ```
///
/// ## Range Queries
///
/// ```rust
/// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
/// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
///
/// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
/// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
/// set.insert(1);
/// set.insert(2);
/// set.insert(3);
///
/// let range: Vec<_> = set.range(2..).collect();
/// assert_eq!(range, vec![2, 3]);
/// ```
///
/// ## Custom Types
///
/// You can store custom types in a `BTreeSet` by implementing the `Storable` trait:
///
/// ```rust
/// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl, Storable};
/// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
/// use std::borrow::Cow;
///
/// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
/// struct CustomType {
///     id: u64,
/// }
///
/// impl Storable for CustomType {
///     fn to_bytes(&self) -> Cow<'_, [u8]> {
///         Cow::Owned(self.id.to_le_bytes().to_vec())
///     }
///
///     fn into_bytes(self) -> Vec<u8> {
///         self.id.to_le_bytes().to_vec()
///     }
///
///     fn from_bytes(bytes: Cow<[u8]>) -> Self {
///         let id = u64::from_le_bytes(bytes.as_ref().try_into().unwrap());
///         CustomType { id }
///     }
///
///     const BOUND: ic_stable_structures::storable::Bound =
///         ic_stable_structures::storable::Bound::Bounded {
///             max_size: 8,
///             is_fixed_size: true,
///         };
/// }
///
/// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
/// let mut set: BTreeSet<CustomType, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
/// set.insert(CustomType { id: 42 });
/// assert!(set.contains(&CustomType { id: 42 }));
/// ```
///
/// ### Bounded vs Unbounded Types
///
/// When implementing `Storable`, you must specify whether your type is bounded or unbounded:
///
/// - **Unbounded (`Bound::Unbounded`)**:
///   - Use when your type's serialized size can vary or has no fixed maximum.
///   - Recommended for most custom types, especially those containing Strings or Vecs.
///   - Example: `const BOUND: Bound = Bound::Unbounded;`
///
/// - **Bounded (`Bound::Bounded{ max_size, is_fixed_size }`)**:
///   - Use when you know the maximum serialized size of your type.
///   - Enables memory optimizations in the `BTreeSet`.
///   - Example: `const BOUND: Bound = Bound::Bounded { max_size: 100, is_fixed_size: false };`
///   - For types with truly fixed size (like primitive types), set `is_fixed_size: true`.
///
/// If unsure, use `Bound::Unbounded` as it's the safer choice.
///
/// # Warning
///
/// Once you've deployed with a bounded type, you cannot increase its `max_size` in
/// future versions without risking data corruption. You can, however, migrate from a bounded type
/// to an unbounded type if needed. For evolving data structures, prefer `Bound::Unbounded`.
pub struct BTreeSet<K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    // The underlying implementation uses a BTreeMap with unit values.
    // This design allows us to reuse the existing BTreeMap implementation.
    // However, if needed, this could be optimized in the future to avoid
    // the overhead of storing unit values.
    map: BTreeMap<K, (), M>,
}

impl<K, M> BTreeSet<K, M>
where
    K: Storable + Ord + Clone,
    M: Memory,
{
    /// Initializes a `BTreeSet`.
    ///
    /// If the memory provided already contains a `BTreeSet`, then that
    /// map is loaded. Otherwise, a new `BTreeSet` instance is created.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let set: BTreeSet<u64, _> = BTreeSet::init(mem_mgr.get(MemoryId::new(0)));
    /// ```
    pub fn init(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::init(memory),
        }
    }

    /// Creates a new instance of a `BTreeSet`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// ```
    pub fn new(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::new(memory),
        }
    }

    /// Loads the `BTreeSet` from memory.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    ///
    /// // Save the set to memory
    /// let memory = set.into_memory();
    ///
    /// // Load the set from memory
    /// let loaded_set: BTreeSet<u64, _> = BTreeSet::load(memory);
    /// assert!(loaded_set.contains(&42));
    /// ```
    pub fn load(memory: M) -> Self {
        BTreeSet {
            map: BTreeMap::<K, (), M>::load(memory),
        }
    }

    /// Inserts a key into the set. Returns `true` if the key
    /// did not exist in the set before.
    ///
    /// # Complexity
    /// O(log n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// assert!(set.insert(42));
    /// assert!(!set.insert(42)); // Key already exists
    /// ```
    pub fn insert(&mut self, key: K) -> bool {
        self.map.insert(key, ()).is_none()
    }

    /// Returns `true` if the key exists in the set, `false` otherwise.
    ///
    /// # Complexity
    /// O(log n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// assert!(set.contains(&42));
    /// assert!(!set.contains(&7));
    /// ```
    pub fn contains(&self, key: &K) -> bool {
        self.map.get(key).is_some()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Complexity
    /// O(1)
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// assert!(set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the number of elements in the set.
    ///
    /// # Complexity
    /// O(1)
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn len(&self) -> u64 {
        self.map.len()
    }

    /// Returns the underlying memory.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// let memory = set.into_memory();
    /// ```
    pub fn into_memory(self) -> M {
        self.map.into_memory()
    }

    /// Removes all elements from the set.
    ///
    /// This operation clears the set by deallocating all memory used by its elements.
    ///
    /// # Complexity
    /// O(n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    /// 
    /// # Safety Note for Bucket Release
    /// If using manual bucket release via `MemoryManager::release_virtual_memory_buckets()`:
    /// 1. Call `clear()` first to clear all data
    /// 2. Call `release_virtual_memory_buckets()` on the memory manager
    /// 3. **MANDATORY**: Drop this BTreeSet object (let it go out of scope)
    /// 4. Create new structures as needed
    /// 
    /// Using this BTreeSet after bucket release causes data corruption.
    pub fn clear(&mut self) {
        self.map.clear_new();
    }

    /// Returns the first key in the set. This key
    /// is the minimum key in the set.
    ///
    /// # Complexity
    /// O(log n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.first(), Some(7));
    /// ```
    pub fn first(&self) -> Option<K> {
        self.map.first_key_value().map(|(a, _)| a)
    }

    /// Returns the last key in the set. This key
    /// is the maximum key in the set.
    ///
    /// # Complexity
    /// O(log n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.last(), Some(42));
    /// ```
    pub fn last(&self) -> Option<K> {
        self.map.last_key_value().map(|(a, _)| a)
    }

    /// Removes a key from the set, returning `true` if it exists.
    ///
    /// # Complexity
    /// O(log n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// assert!(set.remove(&42));
    /// assert!(!set.contains(&42));
    /// ```
    pub fn remove(&mut self, key: &K) -> bool {
        self.map.remove(key).is_some()
    }

    /// Removes and returns the last element in the set. The key of this element is the maximum key that was in the set.
    ///
    /// # Complexity
    /// O(log n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.pop_last(), Some(42));
    /// ```
    pub fn pop_last(&mut self) -> Option<K> {
        self.map.pop_last().map(|(a, _)| a)
    }

    /// Removes and returns the first element in the set. The key of this element is the minimum key that was in the set.
    ///
    /// # Complexity
    /// O(log n), where n is the number of elements in the set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// set.insert(7);
    /// assert_eq!(set.pop_first(), Some(7));
    /// ```
    pub fn pop_first(&mut self) -> Option<K> {
        self.map.pop_first().map(|(a, _)| a)
    }

    /// Returns an iterator over the entries of the set, sorted by key.
    ///
    /// # Complexity
    /// Creating the iterator is O(1), and iterating over k elements is O(k).
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(42);
    /// set.insert(7);
    /// for key in set.iter() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, M> {
        Iter::new(self.map.iter())
    }

    /// Returns an iterator over the entries in the set where keys
    /// belong to the specified range.
    ///
    /// # Complexity
    /// O(log n) for creating the iterator. Iterating over the range is O(k), where k is the number of elements in the range.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// set.insert(1);
    /// set.insert(2);
    /// set.insert(3);
    /// let range: Vec<_> = set.range(2..).collect();
    /// assert_eq!(range, vec![2, 3]);
    /// ```
    pub fn range(&self, key_range: impl RangeBounds<K>) -> Iter<'_, K, M> {
        Iter::new(self.map.range(key_range))
    }

    /// Returns an iterator over the union of this set and another.
    ///
    /// The union of two sets is a set containing all elements that are in either set.
    ///
    /// # Complexity
    /// O(n + m), where:
    /// - n is the size of the first set.
    /// - m is the size of the second set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set1: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// let mut set2: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(1)));
    ///
    /// set1.insert(1);
    /// set1.insert(2);
    /// set2.insert(2);
    /// set2.insert(3);
    ///
    /// let union: Vec<_> = set1.union(&set2).collect();
    /// assert_eq!(union, vec![1, 2, 3]);
    /// ```
    pub fn union<'a>(&'a self, other: &'a BTreeSet<K, M>) -> impl Iterator<Item = K> + 'a {
        let mut iter_self = self.iter();
        let mut iter_other = other.iter();
        let mut next_self = iter_self.next();
        let mut next_other = iter_other.next();

        // Use a closure to merge the two iterators while maintaining sorted order.
        std::iter::from_fn(move || {
            match (next_self.clone(), next_other.clone()) {
                // If both iterators have elements, compare the current elements.
                (Some(ref a), Some(ref b)) => match a.cmp(b) {
                    std::cmp::Ordering::Less => {
                        // If the element from `self` is smaller, yield it and advance `self`.
                        next_self = iter_self.next();
                        Some(a.clone())
                    }
                    std::cmp::Ordering::Greater => {
                        // If the element from `other` is smaller, yield it and advance `other`.
                        next_other = iter_other.next();
                        Some(b.clone())
                    }
                    std::cmp::Ordering::Equal => {
                        // If the elements are equal, yield one and advance both iterators.
                        next_self = iter_self.next();
                        next_other = iter_other.next();
                        Some(a.clone())
                    }
                },
                // If only `self` has elements remaining, yield them.
                (Some(ref a), None) => {
                    next_self = iter_self.next();
                    Some(a.clone())
                }
                // If only `other` has elements remaining, yield them.
                (None, Some(ref b)) => {
                    next_other = iter_other.next();
                    Some(b.clone())
                }
                // If both iterators are exhausted, stop the iteration.
                (None, None) => None,
            }
        })
    }

    /// Returns an iterator over the intersection of this set and another.
    ///
    /// The intersection of two sets is a set containing only the elements that are in both sets.
    ///
    /// # Complexity
    /// O(n + m), where:
    /// - n is the size of the first set.
    /// - m is the size of the second set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set1: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// let mut set2: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(1)));
    ///
    /// set1.insert(1);
    /// set1.insert(2);
    /// set1.insert(3);
    ///
    /// set2.insert(2);
    /// set2.insert(3);
    /// set2.insert(4);
    ///
    /// let intersection: Vec<_> = set1.intersection(&set2).collect();
    /// assert_eq!(intersection, vec![2, 3]);
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a BTreeSet<K, M>) -> impl Iterator<Item = K> + 'a {
        let mut iter_self = self.iter();
        let mut iter_other = other.iter();
        let mut next_self = iter_self.next();
        let mut next_other = iter_other.next();

        // Use a closure to find common elements by traversing both iterators simultaneously.
        std::iter::from_fn(move || {
            // Loop until we find a common element or exhaust either iterator.
            while let (Some(ref a), Some(ref b)) = (next_self.clone(), next_other.clone()) {
                match a.cmp(b) {
                    std::cmp::Ordering::Less => {
                        // If the element from `self` is smaller, advance `self`.
                        next_self = iter_self.next();
                    }
                    std::cmp::Ordering::Greater => {
                        // If the element from `other` is smaller, advance `other`.
                        next_other = iter_other.next();
                    }
                    std::cmp::Ordering::Equal => {
                        // If the elements are equal, yield one and advance both iterators.
                        next_self = iter_self.next();
                        next_other = iter_other.next();
                        return Some(a.clone());
                    }
                }
            }
            // Stop the iteration when either iterator is exhausted.
            None
        })
    }

    /// Returns `true` if this set has no elements in common with another set.
    ///
    /// # Complexity
    /// O(n + m), where:
    /// - n is the size of the first set.
    /// - m is the size of the second set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set1: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// let mut set2: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(1)));
    ///
    /// set1.insert(1);
    /// set1.insert(2);
    /// set2.insert(3);
    /// set2.insert(4);
    ///
    /// assert!(set1.is_disjoint(&set2));
    /// set2.insert(2);
    /// assert!(!set1.is_disjoint(&set2));
    /// ```
    pub fn is_disjoint(&self, other: &BTreeSet<K, M>) -> bool {
        let mut iter_self = self.iter();
        let mut iter_other = other.iter();
        let mut next_self = iter_self.next();
        let mut next_other = iter_other.next();

        while let (Some(a), Some(b)) = (next_self.as_ref(), next_other.as_ref()) {
            match a.cmp(b) {
                std::cmp::Ordering::Less => next_self = iter_self.next(),
                std::cmp::Ordering::Greater => next_other = iter_other.next(),
                std::cmp::Ordering::Equal => return false, // Common element found
            }
        }

        true // No common elements
    }

    /// Returns `true` if this set is a subset of another set.
    ///
    /// A set `A` is a subset of a set `B` if all elements of `A` are also elements of `B`.
    ///
    /// # Complexity
    /// O(n + m), where:
    /// - n is the size of the first set.
    /// - m is the size of the second set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set1: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// let mut set2: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(1)));
    ///
    /// set1.insert(1);
    /// set1.insert(2);
    /// set2.insert(1);
    /// set2.insert(2);
    /// set2.insert(3);
    ///
    /// assert!(set1.is_subset(&set2));
    /// assert!(!set2.is_subset(&set1));
    /// ```
    pub fn is_subset(&self, other: &BTreeSet<K, M>) -> bool {
        let mut self_iter = self.iter();
        let mut other_iter = other.iter();

        let mut self_next = self_iter.next();
        let mut other_next = other_iter.next();

        while let Some(ref self_key) = self_next {
            match other_next {
                Some(ref other_key) => match self_key.cmp(other_key) {
                    std::cmp::Ordering::Equal => {
                        // Keys match, advance both iterators.
                        self_next = self_iter.next();
                        other_next = other_iter.next();
                    }
                    std::cmp::Ordering::Greater => {
                        // Advance the `other` iterator if its key is smaller.
                        other_next = other_iter.next();
                    }
                    std::cmp::Ordering::Less => {
                        // `self_key` is smaller than the current smallest item of
                        // other which means that it cannot be found in `other`,
                        // so return false.
                        return false;
                    }
                },
                None => {
                    // If `other` is exhausted but `self` is not, return false.
                    return false;
                }
            }
        }

        // If we exhaust `self`, it is a subset of `other`.
        true
    }

    /// Returns `true` if this set is a superset of another set.
    ///
    /// A set `A` is a superset of a set `B` if all elements of `B` are also elements of `A`.
    ///
    /// # Complexity
    /// O(n + m), where:
    /// - n is the size of the first set.
    /// - m is the size of the second set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set1: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// let mut set2: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(1)));
    ///
    /// set1.insert(1);
    /// set1.insert(2);
    /// set1.insert(3);
    /// set2.insert(1);
    /// set2.insert(2);
    ///
    /// assert!(set1.is_superset(&set2));
    /// assert!(!set2.is_superset(&set1));
    /// ```
    pub fn is_superset(&self, other: &BTreeSet<K, M>) -> bool {
        other.is_subset(self)
    }

    /// Returns an iterator over the symmetric difference of this set and another.
    ///
    /// The symmetric difference of two sets is the set of elements that are in either of the sets,
    /// but not in their intersection.
    ///
    /// # Complexity
    /// O(n + m), where:
    /// - n is the size of the first set.
    /// - m is the size of the second set.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeSet, DefaultMemoryImpl};
    /// use ic_stable_structures::memory_manager::{MemoryId, MemoryManager};
    ///
    /// let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
    /// let mut set1: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(0)));
    /// let mut set2: BTreeSet<u64, _> = BTreeSet::new(mem_mgr.get(MemoryId::new(1)));
    ///
    /// set1.insert(1);
    /// set1.insert(2);
    /// set2.insert(2);
    /// set2.insert(3);
    ///
    /// let symmetric_diff: Vec<_> = set1.symmetric_difference(&set2).collect();
    /// assert_eq!(symmetric_diff, vec![1, 3]);
    /// ```
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a BTreeSet<K, M>,
    ) -> impl Iterator<Item = K> + 'a {
        let mut iter_self = self.iter();
        let mut iter_other = other.iter();
        let mut next_self = iter_self.next();
        let mut next_other = iter_other.next();

        // Use a closure to find common elements by traversing both iterators simultaneously.
        std::iter::from_fn(move || {
            // Loop until we detect a difference or exhaust either iterator.
            loop {
                return match (next_self.clone(), next_other.clone()) {
                    (Some(ref a), Some(ref b)) => {
                        match a.cmp(b) {
                            std::cmp::Ordering::Less => {
                                // If the element from `self` is smaller, yield it and advance `self`.
                                next_self = iter_self.next();
                                Some(a.clone())
                            }
                            std::cmp::Ordering::Greater => {
                                // If the element from `other` is smaller, yield it and advance `other`.
                                next_other = iter_other.next();
                                Some(b.clone())
                            }
                            std::cmp::Ordering::Equal => {
                                // Skip elements that are in both sets and advance both iterators.
                                next_self = iter_self.next();
                                next_other = iter_other.next();
                                continue;
                            }
                        }
                    }
                    (Some(ref a), None) => {
                        // If only `self` has elements remaining, yield them.
                        next_self = iter_self.next();
                        Some(a.clone())
                    }
                    (None, Some(ref b)) => {
                        // If only `other` has elements remaining, yield them.
                        next_other = iter_other.next();
                        Some(b.clone())
                    }
                    (None, None) => None,
                };
            }
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::storable::Blob;
    use crate::VectorMemory;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// Creates a new shared memory instance.
    pub(crate) fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    pub(crate) fn b(x: &[u8]) -> Blob<10> {
        Blob::<10>::try_from(x).unwrap()
    }

    /// A test runner that runs the test using `BTreeSet`.
    pub fn run_btree_test<K, R, F>(f: F)
    where
        K: Storable + Ord + Clone,
        F: Fn(BTreeSet<K, VectorMemory>) -> R,
    {
        let mem = make_memory();
        let btree = BTreeSet::new(mem);
        f(btree);
    }

    #[test]
    fn test_union_with_duplicates() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);
        set1.insert(3);

        set2.insert(2);
        set2.insert(3);
        set2.insert(4);

        let union: Vec<_> = set1.union(&set2).collect();
        assert_eq!(union, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_intersection_with_duplicates() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);
        set1.insert(3);

        set2.insert(2);
        set2.insert(3);
        set2.insert(4);

        let intersection: Vec<_> = set1.intersection(&set2).collect();
        assert_eq!(intersection, vec![2, 3]);
    }

    #[test]
    fn test_union_and_intersection_with_identical_sets() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..100 {
            set1.insert(i);
            set2.insert(i);
        }

        let union: Vec<_> = set1.union(&set2).collect();
        assert_eq!(union.len(), 100);
        assert_eq!(union, (0..100).collect::<Vec<_>>());

        let intersection: Vec<_> = set1.intersection(&set2).collect();
        assert_eq!(intersection.len(), 100);
        assert_eq!(intersection, (0..100).collect::<Vec<_>>());
    }

    #[test]
    fn test_union_and_intersection_with_disjoin_sets() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..50 {
            set1.insert(i);
        }
        for i in 50..100 {
            set2.insert(i);
        }

        let union: Vec<_> = set1.union(&set2).collect();
        assert_eq!(union.len(), 100);
        assert_eq!(union, (0..100).collect::<Vec<_>>());

        let intersection: Vec<_> = set1.intersection(&set2).collect();
        assert!(intersection.is_empty());
    }

    #[test]
    fn test_union_with_large_sets() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            set1.insert(i);
        }
        for i in 500..1500 {
            set2.insert(i);
        }

        let union: Vec<_> = set1.union(&set2).collect();
        assert_eq!(union.len(), 1500);
        assert_eq!(union[0], 0);
        assert_eq!(union[1499], 1499);
    }

    #[test]
    fn test_union_odd_even() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            if i % 2 != 0 {
                set1.insert(i);
            } else {
                set2.insert(i);
            }
        }

        let intersection: Vec<_> = set1.union(&set2).collect();
        assert_eq!(intersection.len(), 1000);
        assert_eq!(intersection, (0..1000).collect::<Vec<_>>());
    }

    #[test]
    fn test_intersection_even() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            set1.insert(i);
            if i % 2 == 0 {
                set2.insert(i);
            }
        }

        let intersection: Vec<_> = set1.intersection(&set2).collect();
        assert_eq!(intersection.len(), 500);
        assert_eq!(intersection, set2.iter().collect::<Vec<_>>());
    }

    #[test]
    fn test_intersection_with_large_sets() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            set1.insert(i);
        }
        for i in 500..1500 {
            set2.insert(i);
        }

        let intersection: Vec<_> = set1.intersection(&set2).collect();
        assert_eq!(intersection.len(), 500);
        assert_eq!(intersection[0], 500);
        assert_eq!(intersection[499], 999);
    }

    #[test]
    fn init_preserves_data_set() {
        run_btree_test(|mut btree| {
            assert!(btree.insert(b(&[1, 2, 3])));
            assert!(btree.contains(&b(&[1, 2, 3])));

            // Reload the btree
            let btree = BTreeSet::init(btree.into_memory());

            // Data still exists.
            assert!(btree.contains(&b(&[1, 2, 3])));
        });
    }

    #[test]
    fn test_insert_and_contains() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        assert!(!btreeset.contains(&1u32));
        btreeset.insert(1u32);
        assert!(btreeset.contains(&1u32));
    }

    #[test]
    fn test_remove() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(1u32);
        assert!(btreeset.contains(&1u32));
        btreeset.remove(&1u32);
        assert!(!btreeset.contains(&1u32));
    }

    #[test]
    fn test_iter() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(1u32);
        btreeset.insert(2u32);
        btreeset.insert(3u32);

        let elements: Vec<_> = btreeset.iter().collect();
        assert_eq!(elements, vec![1u32, 2u32, 3u32]);
    }

    #[test]
    fn test_range() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        for i in 1u32..=10 {
            btreeset.insert(i);
        }

        let range: Vec<_> = btreeset.range(4u32..8u32).collect();
        assert_eq!(range, vec![4u32, 5u32, 6u32, 7u32]);
    }

    #[test]
    fn test_first_and_last() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(3u32);
        btreeset.insert(1u32);
        btreeset.insert(2u32);

        assert_eq!(btreeset.first(), Some(1u32));
        assert_eq!(btreeset.last(), Some(3u32));
    }

    #[test]
    fn test_len_and_is_empty() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        assert!(btreeset.is_empty());
        assert_eq!(btreeset.len(), 0);

        btreeset.insert(1u32);
        assert!(!btreeset.is_empty());
        assert_eq!(btreeset.len(), 1);
    }

    #[test]
    fn test_pop_first_and_last() {
        let mem = make_memory();
        let mut btreeset = BTreeSet::new(mem);

        btreeset.insert(3u32);
        btreeset.insert(1u32);
        btreeset.insert(2u32);

        assert_eq!(btreeset.pop_first(), Some(1u32));
        assert_eq!(btreeset.pop_last(), Some(3u32));
        assert_eq!(btreeset.len(), 1);
        assert_eq!(btreeset.first(), Some(2u32));
        assert_eq!(btreeset.last(), Some(2u32));
    }

    #[test]
    fn test_clear() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        btreeset.insert(1);
        btreeset.insert(2);
        btreeset.insert(3);

        assert_eq!(btreeset.len(), 3);
        btreeset.clear();
        assert!(btreeset.is_empty());
        assert_eq!(btreeset.len(), 0);
        assert_eq!(btreeset.iter().next(), None);
    }

    #[test]
    fn test_iterate_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1000 {
            btreeset.insert(i);
        }

        let elements: Vec<_> = btreeset.iter().collect();
        assert_eq!(elements.len(), 1000);
        assert_eq!(elements[0], 0);
        assert_eq!(elements[999], 999);
    }

    #[test]
    fn test_range_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0u32..1000 {
            btreeset.insert(i);
        }

        let range: Vec<_> = btreeset.range(100..200).collect();
        assert_eq!(range.len(), 100);
        assert_eq!(range[0], 100);
        assert_eq!(range[99], 199);
    }

    #[test]
    fn test_empty_set() {
        let mem = make_memory();
        let btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert!(btreeset.is_empty());
        assert_eq!(btreeset.len(), 0);
        assert_eq!(btreeset.first(), None);
        assert_eq!(btreeset.last(), None);
        assert_eq!(btreeset.iter().next(), None);
    }

    #[test]
    fn test_insert_duplicate() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert!(btreeset.insert(42));
        assert!(!btreeset.insert(42)); // Duplicate insert
        assert_eq!(btreeset.len(), 1);
        assert!(btreeset.contains(&42));
    }

    #[test]
    fn test_remove_nonexistent() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert!(!btreeset.remove(&42)); // Removing a non-existent element
        assert!(btreeset.is_empty());
    }

    #[test]
    fn test_pop_first_and_last_empty() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        assert_eq!(btreeset.pop_first(), None);
        assert_eq!(btreeset.pop_last(), None);
    }

    #[test]
    fn test_range_empty() {
        let mem = make_memory();
        let btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        let range: Vec<_> = btreeset.range(10..20).collect();
        assert!(range.is_empty());
    }

    #[test]
    fn test_insert_and_remove_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1_000 {
            assert!(btreeset.insert(i));
        }
        assert_eq!(btreeset.len(), 1_000);

        for i in 0..1_000 {
            assert!(btreeset.remove(&i));
        }
        assert!(btreeset.is_empty());
    }

    #[test]
    fn test_remove_nonexistent_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1_000 {
            assert!(btreeset.insert(i));
        }

        for i in 1_000..2_000 {
            assert!(!btreeset.remove(&i)); // Non-existent elements
        }
        assert_eq!(btreeset.len(), 1_000);
    }

    #[test]
    fn test_iterate_empty_set() {
        let mem = make_memory();
        let btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        let elements: Vec<_> = btreeset.iter().collect();
        assert!(elements.is_empty());
    }

    #[test]
    fn test_range_with_no_matches() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..10 {
            btreeset.insert(i);
        }

        let range: Vec<_> = btreeset.range(20..30).collect();
        assert!(range.is_empty());
    }

    #[test]
    fn test_clear_and_reuse() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..100 {
            btreeset.insert(i);
        }
        assert_eq!(btreeset.len(), 100);

        btreeset.clear();
        assert!(btreeset.is_empty());

        for i in 100..200 {
            btreeset.insert(i);
        }
        assert_eq!(btreeset.len(), 100);
        assert!(btreeset.contains(&150));
    }

    #[test]
    fn test_pop_first_and_last_large_set() {
        let mem = make_memory();
        let mut btreeset: BTreeSet<u32, _> = BTreeSet::new(mem);

        for i in 0..1_000 {
            btreeset.insert(i);
        }

        for i in 0..500 {
            assert_eq!(btreeset.pop_first(), Some(i));
        }

        for i in (500..1_000).rev() {
            assert_eq!(btreeset.pop_last(), Some(i));
        }

        assert!(btreeset.is_empty());
    }

    #[test]
    fn test_is_disjoint_with_disjoint_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);

        set2.insert(3);
        set2.insert(4);

        assert!(set1.is_disjoint(&set2));
    }

    #[test]
    fn test_is_disjoint_with_overlapping_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);

        set2.insert(2);
        set2.insert(3);

        assert!(!set1.is_disjoint(&set2));
    }

    #[test]
    fn test_is_disjoint_with_large_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            set1.insert(i);
        }
        for i in 1000..2000 {
            set2.insert(i);
        }

        assert!(set1.is_disjoint(&set2));

        set2.insert(500);
        assert!(!set1.is_disjoint(&set2));
    }

    #[test]
    fn test_is_subset_with_subset() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);

        set2.insert(1);
        set2.insert(2);
        set2.insert(3);

        assert!(set1.is_subset(&set2));
    }

    #[test]
    fn test_is_subset_with_non_subset() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(4);

        set2.insert(1);
        set2.insert(2);
        set2.insert(3);

        assert!(!set1.is_subset(&set2));
    }

    #[test]
    fn test_is_subset_with_large_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..500 {
            set1.insert(i);
        }
        for i in 0..1500 {
            set2.insert(i);
        }

        assert!(set1.is_subset(&set2));

        set1.insert(1500);
        assert!(!set1.is_subset(&set2));
    }

    #[test]
    fn test_is_superset_with_superset() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);
        set1.insert(3);

        set2.insert(1);
        set2.insert(2);

        assert!(set1.is_superset(&set2));
    }

    #[test]
    fn test_is_superset_with_non_superset() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);

        set2.insert(1);
        set2.insert(3);

        assert!(!set1.is_superset(&set2));
    }

    #[test]
    fn test_is_superset_with_large_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            set1.insert(i);
        }
        for i in 500..1000 {
            set2.insert(i);
        }

        assert!(set1.is_superset(&set2));

        set2.insert(1500);
        assert!(!set1.is_superset(&set2));
    }

    #[test]
    fn test_symmetric_difference_with_disjoint_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);

        set2.insert(3);
        set2.insert(4);

        let symmetric_diff: Vec<_> = set1.symmetric_difference(&set2).collect();
        assert_eq!(symmetric_diff, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_symmetric_difference_with_overlapping_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);
        set1.insert(3);

        set2.insert(2);
        set2.insert(3);
        set2.insert(4);

        let symmetric_diff: Vec<_> = set1.symmetric_difference(&set2).collect();
        assert_eq!(symmetric_diff, vec![1, 4]);
    }

    #[test]
    fn test_symmetric_difference_with_identical_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        set1.insert(1);
        set1.insert(2);
        set1.insert(3);

        set2.insert(1);
        set2.insert(2);
        set2.insert(3);

        let symmetric_diff: Vec<_> = set1.symmetric_difference(&set2).collect();
        assert!(symmetric_diff.is_empty());
    }

    #[test]
    fn test_symmetric_difference_with_large_sets() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            set1.insert(i);
        }
        for i in 500..1500 {
            set2.insert(i);
        }

        let symmetric_diff: Vec<_> = set1.symmetric_difference(&set2).collect();
        assert_eq!(symmetric_diff.len(), 1000);
        assert_eq!(symmetric_diff[..500], (0..500).collect::<Vec<_>>());
        assert_eq!(symmetric_diff[500..], (1000..1500).collect::<Vec<_>>());
    }

    #[test]
    fn test_symmetric_difference_odd_even() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in 0..1000 {
            if i % 2 != 0 {
                set1.insert(i);
            } else {
                set2.insert(i);
            }
        }

        let intersection: Vec<_> = set1.symmetric_difference(&set2).collect();
        assert_eq!(intersection.len(), 1000);
        assert_eq!(intersection, (0..1000).collect::<Vec<_>>());
    }

    #[test]
    fn test_symmetric_difference_even() {
        let mem1 = Rc::new(RefCell::new(Vec::new()));
        let mem2 = Rc::new(RefCell::new(Vec::new()));
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        let mut expected_res = vec![];

        for i in 0..1000 {
            set1.insert(i);

            if i % 2 == 0 {
                set2.insert(i);
            } else {
                expected_res.push(i);
            }
        }

        let intersection: Vec<_> = set1.symmetric_difference(&set2).collect();
        assert_eq!(intersection.len(), 500);
        assert_eq!(intersection, expected_res);
    }

    #[test]
    fn test_is_subset_with_sparse_elements() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in (0..1000).step_by(10) {
            set1.insert(i);
        }
        for i in (0..2000).step_by(5) {
            set2.insert(i);
        }

        assert!(set1.is_subset(&set2));

        set1.insert(2001);
        assert!(!set1.is_subset(&set2));
    }

    #[test]
    fn test_is_disjoint_with_sparse_elements() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in (0..1000).step_by(10) {
            set1.insert(i);
        }
        for i in (1..1000).step_by(10) {
            set2.insert(i);
        }

        assert!(set1.is_disjoint(&set2));

        set2.insert(20);
        assert!(!set1.is_disjoint(&set2));
    }

    #[test]
    fn test_is_superset_with_sparse_elements() {
        let mem1 = make_memory();
        let mem2 = make_memory();
        let mut set1: BTreeSet<u32, _> = BTreeSet::new(mem1);
        let mut set2: BTreeSet<u32, _> = BTreeSet::new(mem2);

        for i in (0..2000).step_by(5) {
            set1.insert(i);
        }
        for i in (0..1000).step_by(10) {
            set2.insert(i);
        }

        assert!(set1.is_superset(&set2));

        set2.insert(2001);
        assert!(!set1.is_superset(&set2));
    }
}
