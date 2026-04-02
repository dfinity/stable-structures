//! This module implements a key/value store based on a B-Tree
//! in stable memory.
//!
//! # V2 layout
//!
//! ```text
//! ---------------------------------------- <- Address 0
//! Magic "BTR"                 ↕ 3 bytes
//! ----------------------------------------
//! Layout version              ↕ 1 byte
//! ----------------------------------------
//! Max key size                ↕ 4 bytes             Page size                   ↕ 4 bytes
//! ----------------------------------------   OR   ----------------------------------------
//! Max value size              ↕ 4 bytes             PAGE_SIZE_VALUE_MARKER      ↕ 4 bytes
//! ----------------------------------------
//! Root node address           ↕ 8 bytes
//! ----------------------------------------
//! Length (number of elements) ↕ 8 bytes
//! ---------------------------------------- <- Address 28 (PACKED_HEADER_SIZE)
//! Reserved space              ↕ 24 bytes
//! ---------------------------------------- <- Address 52 (ALLOCATOR_OFFSET)
//! Allocator
//! ----------------------------------------
//! ... free memory for nodes
//! ----------------------------------------
//! ```
//!
//! # V1 layout
//!
//! ```text
//! ---------------------------------------- <- Address 0
//! Magic "BTR"                 ↕ 3 bytes
//! ----------------------------------------
//! Layout version              ↕ 1 byte
//! ----------------------------------------
//! Max key size                ↕ 4 bytes
//! ----------------------------------------
//! Max value size              ↕ 4 bytes
//! ----------------------------------------
//! Root node address           ↕ 8 bytes
//! ----------------------------------------
//! Length (number of elements) ↕ 8 bytes
//! ---------------------------------------- <- Address 28 (PACKED_HEADER_SIZE)
//! Reserved space              ↕ 24 bytes
//! ---------------------------------------- <- Address 52 (ALLOCATOR_OFFSET)
//! Allocator
//! ----------------------------------------
//! ... free memory for nodes
//! ----------------------------------------
//! ```
mod allocator;
mod iter;
mod node;
mod node_cache;
use crate::btreemap::iter::{IterInternal, KeysIter, ValuesIter};
use crate::{
    storable::Bound as StorableBound,
    types::{Address, NULL},
    Memory, Storable,
};
use allocator::Allocator;
pub use iter::Iter;
use node::{DerivedPageSize, Entry, Node, NodeType, PageSize, Version};
use node_cache::NodeCache;
pub use node_cache::NodeCacheMetrics;
use std::borrow::Cow;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};

#[cfg(test)]
mod proptests;

const MAGIC: &[u8; 3] = b"BTR";
const LAYOUT_VERSION: u8 = 1;
const LAYOUT_VERSION_2: u8 = 2;
// The sum of all the header fields, i.e. size of a packed header.
const PACKED_HEADER_SIZE: usize = 28;
// The offset where the allocator begins.
const ALLOCATOR_OFFSET: usize = 52;

// The default page size to use in BTreeMap V2 in bytes.
const DEFAULT_PAGE_SIZE: u32 = 1024;

// A marker to indicate that the `PageSize` stored in the header is a `PageSize::Value`.
const PAGE_SIZE_VALUE_MARKER: u32 = u32::MAX;

/// Default number of slots in the direct-mapped node cache.
///
/// 16 slots cover the top two tree levels (1 root + up to 12 children =
/// 13 nodes) while keeping heap usage modest.
///
/// Users can adjust via [`BTreeMap::with_node_cache`] or
/// [`BTreeMap::node_cache_resize`], including setting to 0 to disable.
const DEFAULT_NODE_CACHE_NUM_SLOTS: usize = 16;

/// A B-Tree map implementation that stores its data into a designated memory.
///
/// # Memory Implementations
///
/// `BTreeMap` works with any memory implementation that satisfies the [`Memory`] trait:
///
/// - [`Ic0StableMemory`](crate::Ic0StableMemory): Stores data in the Internet Computer's stable memory
/// - [`VectorMemory`](crate::VectorMemory): In-memory implementation backed by a Rust `Vec<u8>`
/// - [`FileMemory`](crate::FileMemory): Persists data to disk using a file
/// - [`DefaultMemoryImpl`](crate::DefaultMemoryImpl): Default implementation that automatically selects the
///   appropriate memory backend based on the environment:
///   - Uses `Ic0StableMemory` when running in an Internet Computer canister (wasm32 target)
///   - Falls back to `VectorMemory` in other environments (like tests or non-IC contexts)
///
/// For almost all use cases, [`DefaultMemoryImpl`](crate::DefaultMemoryImpl) is recommended as it provides
/// the right implementation based on the runtime context.
///
/// # Examples
///
/// ## Basic Usage with a Single BTreeMap
///
/// ```rust
/// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
/// let mut map: BTreeMap<u64, String, _> = BTreeMap::init(DefaultMemoryImpl::default());
///
/// map.insert(1, "hello".to_string());
/// # assert_eq!(map.get(&1), Some("hello".to_string()));
/// ```
///
/// ## Multiple BTreeMaps and Memory Management
///
/// **Important**: Each stable structure requires its own designated memory region. Attempting to
/// initialize multiple structures with the same memory will lead to data corruption.
///
/// ### What NOT to do:
///
/// ```rust,no_run
/// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
///
/// // ERROR: Using the same memory for multiple BTreeMaps will corrupt data
/// let mut map_1: BTreeMap<u64, String, _> = BTreeMap::init(DefaultMemoryImpl::default());
/// let mut map_2: BTreeMap<u64, String, _> = BTreeMap::init(DefaultMemoryImpl::default());
///
/// map_1.insert(1, "two".to_string());
/// map_2.insert(1, "three".to_string());
/// // This assertion would fail: changes to map_2 corrupt map_1's data
/// assert_eq!(map_1.get(&1), Some("two".to_string()));
/// ```
///
/// ### Correct approach using MemoryManager:
///
/// ```rust
/// use ic_stable_structures::{
///    memory_manager::{MemoryId, MemoryManager},
///    BTreeMap, DefaultMemoryImpl,
/// };
///
/// // Initialize the memory manager with a single memory
/// let memory_manager = MemoryManager::init(DefaultMemoryImpl::default());
///
/// // Get separate virtual memories for each BTreeMap
/// let mut map_1: BTreeMap<u64, String, _> = BTreeMap::init(memory_manager.get(MemoryId::new(0)));
/// let mut map_2: BTreeMap<u64, String, _> = BTreeMap::init(memory_manager.get(MemoryId::new(1)));
///
/// map_1.insert(1, "two".to_string());
/// map_2.insert(1, "three".to_string());
/// // Now this works as expected
/// assert_eq!(map_1.get(&1), Some("two".to_string()));
/// ```
///
/// The [`MemoryManager`](crate::memory_manager::MemoryManager) creates up to 255 virtual memories
/// from a single contiguous memory, allowing multiple stable structures to safely coexist.
///
/// For complete examples of using multiple stable structures in a production environment, see the
/// [Quick Start example](https://github.com/dfinity/stable-structures/tree/main/examples/src/quick_start).
///
/// ## Custom Types
///
/// You can store custom structs in a `BTreeMap` by implementing the `Storable` trait:
///
/// ```rust
/// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl, Storable, storable::Bound};
/// use std::borrow::Cow;
///
/// #[derive(Debug, PartialEq)]
/// struct User {
///     id: u64,
///     name: String,
/// }
///
/// impl Storable for User {
///     fn to_bytes(&self) -> Cow<'_, [u8]> {
///         let mut bytes = Vec::new();
///         // TODO: Convert your struct to bytes...
///         Cow::Owned(bytes)
///     }
///
///     fn into_bytes(self) -> Vec<u8> {
///         let mut bytes = Vec::new();
///         // TODO: Convert your struct to bytes...
///         bytes
///     }
///
///     fn from_bytes(bytes: Cow<[u8]>) -> Self {
///         // TODO: Convert bytes back to your struct
///         let (id, name) = (0, "".to_string());
///         User { id, name }
///     }
///
///     // Types can be bounded or unbounded:
///     // - Use Bound::Unbounded if the size can vary or isn't known in advance (recommended for most cases)
///     // - Use Bound::Bounded if you know the maximum size and want memory optimization
///     const BOUND: Bound = Bound::Unbounded;
/// }
///
/// // Now you can use your custom type in a BTreeMap
/// let mut map: BTreeMap<u64, User, _> = BTreeMap::init(DefaultMemoryImpl::default());
///
/// let user = User { id: 1, name: "Alice".to_string() };
/// map.insert(1, user);
///
/// // Retrieving the custom type
/// if let Some(user) = map.get(&1) {
///     println!("Found user: {}", user.name);
/// }
/// ```
///
/// ### Bounded vs Unbounded Types
///
/// When implementing `Storable`, you must specify whether your type is bounded or unbounded:
///
/// - **Unbounded (`Bound::Unbounded`)**:
///   - Use when your type's serialized size can vary or has no fixed maximum
///   - Recommended for most custom types, especially those containing Strings or Vecs
///   - Example: `const BOUND: Bound = Bound::Unbounded;`
///
/// - **Bounded (`Bound::Bounded{ max_size, is_fixed_size }`)**:
///   - Use when you know the maximum serialized size of your type
///   - Enables memory optimizations in the BTreeMap
///   - Example: `const BOUND: Bound = Bound::Bounded { max_size: 100, is_fixed_size: false };`
///   - For types with truly fixed size (like primitive types), set `is_fixed_size: true`
///
/// If unsure, use `Bound::Unbounded` as it's the safer choice.
///
/// # Warning
///
/// Once you've deployed with a bounded type, you cannot increase its `max_size` in
/// future versions without risking data corruption. You can, however, migrate from a bounded type
/// to an unbounded type if needed. For evolving data structures, prefer `Bound::Unbounded`.
pub struct BTreeMap<K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    // The address of the root node. If a root node doesn't exist, the address
    // is set to NULL.
    root_addr: Address,

    version: Version,

    // An allocator used for managing memory and allocating nodes.
    allocator: Allocator<M>,

    // The number of elements in the map.
    length: u64,

    // Direct-mapped node cache to avoid re-loading hot nodes from stable memory.
    cache: RefCell<NodeCache<K>>,

    // A marker to communicate to the Rust compiler that we own these types.
    _phantom: PhantomData<(K, V)>,
}

#[derive(PartialEq, Debug)]
/// The packed header size must be <= ALLOCATOR_OFFSET.
struct BTreeHeader {
    version: Version,
    root_addr: Address,
    length: u64,
    // Reserved bytes for future extensions
}

impl<K, V, M> BTreeMap<K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    /// Initializes a `BTreeMap`.
    ///
    /// If the memory provided already contains a `BTreeMap`, then that
    /// map is loaded. Otherwise, a new `BTreeMap` instance is created.
    pub fn init(memory: M) -> Self {
        if memory.size() == 0 {
            // Memory is empty. Create a new map.
            return BTreeMap::new(memory);
        }

        // Check if the magic in the memory corresponds to a BTreeMap.
        let mut dst = vec![0; 3];
        memory.read(0, &mut dst);
        if dst != MAGIC {
            // No BTreeMap found. Create a new instance.
            BTreeMap::new(memory)
        } else {
            // The memory already contains a BTreeMap. Load it.
            BTreeMap::load(memory)
        }
    }

    /// Configures the number of node-cache slots during construction.
    ///
    /// The cache is a direct-mapped cache that keeps frequently accessed
    /// B-tree nodes in heap memory to avoid repeated stable-memory reads.
    /// Each slot can hold one deserialized node; on collision, shallower
    /// nodes (closer to the root) are kept over deeper ones.
    ///
    /// Pass `0` to disable the cache (the default).
    ///
    /// The top 2 levels of the tree contain 13 nodes (1 root + up to
    /// 12 children). **16** slots is the smallest power of two that
    /// covers them, but a direct-mapped cache is sensitive to address
    /// collisions, so **32** is a safer default that leaves headroom
    /// and typically gives 2 cache hits per operation regardless of
    /// tree size. Prefer powers of two for efficient slot indexing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let map: BTreeMap<u64, u64, _> =
    ///     BTreeMap::init(DefaultMemoryImpl::default())
    ///         .with_node_cache(32);
    /// ```
    pub fn with_node_cache(mut self, num_slots: usize) -> Self {
        self.node_cache_resize(num_slots);
        self
    }

    /// Resizes the node cache at runtime.
    ///
    /// Existing cache contents and performance counters are discarded.
    ///
    /// Pass `0` to disable the cache entirely.
    ///
    /// See [`with_node_cache`](Self::with_node_cache) for guidance on
    /// choosing a size.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let mut map: BTreeMap<u64, u64, _> =
    ///     BTreeMap::init(DefaultMemoryImpl::default())
    ///         .with_node_cache(32);
    ///
    /// // After observing a poor hit ratio, grow the cache.
    /// if map.node_cache_metrics().hit_ratio() < 0.5 {
    ///     map.node_cache_resize(64);
    /// }
    /// ```
    pub fn node_cache_resize(&mut self, num_slots: usize) {
        *self.cache.get_mut() = NodeCache::new(self.version.page_size().get(), num_slots);
    }

    /// Returns the current number of slots in the node cache.
    ///
    /// Returns `0` when the cache is disabled.
    pub fn node_cache_size(&self) -> usize {
        self.cache.borrow().num_slots()
    }

    /// Evicts all cached nodes and resets metrics, keeping the
    /// current cache capacity.
    pub fn node_cache_clear(&mut self) {
        self.cache.get_mut().clear();
    }

    /// Resets cache metrics (hit/miss counters) without evicting
    /// cached nodes.
    pub fn node_cache_clear_metrics(&mut self) {
        self.cache.get_mut().clear_metrics();
    }

    /// Returns node-cache performance metrics.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    ///
    /// let mut map: BTreeMap<u64, u64, _> =
    ///     BTreeMap::init(DefaultMemoryImpl::default())
    ///         .with_node_cache(32);
    /// map.insert(1, 100);
    /// let _ = map.get(&1);
    ///
    /// let metrics = map.node_cache_metrics();
    /// println!("hit ratio: {:.1}%", metrics.hit_ratio() * 100.0);
    /// ```
    pub fn node_cache_metrics(&self) -> NodeCacheMetrics {
        self.cache.borrow().metrics()
    }

    /// Returns a rough estimate of the cache's heap usage in bytes.
    ///
    /// Actual usage depends on key size and how many slots are
    /// occupied. Treat this as an order-of-magnitude guide, not a
    /// precise budget.
    pub fn node_cache_size_bytes_approx(&self) -> usize {
        self.cache.borrow().num_slots()
            * (self.version.page_size().get() as usize + NodeCache::<K>::slot_size())
    }

    /// Initializes a v1 `BTreeMap`.
    ///
    /// This is exposed only in testing.
    #[cfg(test)]
    pub fn init_v1(memory: M) -> Self {
        if memory.size() == 0 {
            // Memory is empty. Create a new map.
            return BTreeMap::new_v1(memory);
        }

        // Check if the magic in the memory corresponds to a BTreeMap.
        let mut dst = vec![0; 3];
        memory.read(0, &mut dst);
        if dst != MAGIC {
            // No BTreeMap found. Create a new instance.
            BTreeMap::new_v1(memory)
        } else {
            // The memory already contains a BTreeMap. Load it, making sure
            // we don't migrate the BTreeMap to v2.
            BTreeMap::load_helper(memory, false)
        }
    }

    /// Creates a new instance a `BTreeMap`.
    ///
    /// The given `memory` is assumed to be exclusively reserved for this data
    /// structure and that it starts at address zero. Typically `memory` will
    /// be an instance of `RestrictedMemory`.
    ///
    /// When initialized, the data structure has the following memory layout:
    ///
    ///    |  BTreeHeader  |  Allocator | ... free memory for nodes |
    ///
    /// See `Allocator` for more details on its own memory layout.
    pub fn new(memory: M) -> Self {
        let page_size = match (K::BOUND, V::BOUND) {
            // The keys and values are both bounded.
            (
                StorableBound::Bounded {
                    max_size: max_key_size,
                    ..
                },
                StorableBound::Bounded {
                    max_size: max_value_size,
                    ..
                },
            ) => {
                // Get the maximum possible node size.
                let max_node_size = Node::<K>::max_size(max_key_size, max_value_size).get();

                // A node can have at most 11 entries, and an analysis has shown that ~70% of all
                // nodes have <= 8 entries. We can therefore use a page size that's 8/11 the
                // maximum size with little performance difference but with a significant storage
                // saving. We round the 8/11 to be 3/4.
                PageSize::Value((max_node_size * 3 / 4) as u32)
            }
            // Use a default page size.
            _ => PageSize::Value(DEFAULT_PAGE_SIZE),
        };

        let btree = Self {
            root_addr: NULL,
            allocator: Allocator::new(
                memory,
                Address::from(ALLOCATOR_OFFSET as u64),
                page_size.get().into(),
            ),
            version: Version::V2(page_size),
            length: 0,
            cache: RefCell::new(NodeCache::new(
                page_size.get(),
                DEFAULT_NODE_CACHE_NUM_SLOTS,
            )),
            _phantom: PhantomData,
        };

        btree.save_header();
        btree
    }

    /// Create a v1 instance of the BTree.
    ///
    /// This is only exposed for testing.
    #[cfg(test)]
    pub fn new_v1(memory: M) -> Self {
        let max_key_size = K::BOUND.max_size();
        let max_value_size = V::BOUND.max_size();

        let version = Version::V1(DerivedPageSize {
            max_key_size,
            max_value_size,
        });

        let btree = Self {
            root_addr: NULL,
            allocator: Allocator::new(
                memory,
                Address::from(ALLOCATOR_OFFSET as u64),
                Node::<K>::max_size(max_key_size, max_value_size),
            ),
            version,
            length: 0,
            cache: RefCell::new(NodeCache::new(
                version.page_size().get(),
                DEFAULT_NODE_CACHE_NUM_SLOTS,
            )),
            _phantom: PhantomData,
        };

        btree.save_header();
        btree
    }

    /// Loads the map from memory.
    pub fn load(memory: M) -> Self {
        Self::load_helper(memory, true)
    }

    /// Loads the map from memory, potentially migrating the map from V1 to V2.
    fn load_helper(memory: M, migrate_to_v2: bool) -> Self {
        // Read the header from memory.
        let header = Self::read_header(&memory);

        let version = match header.version {
            Version::V1(derived_page_size) => {
                // Migrate to V2 if flag is enabled.
                if migrate_to_v2 {
                    Version::V2(PageSize::Derived(derived_page_size))
                } else {
                    // Assert that the bounds are correct.
                    let max_key_size = derived_page_size.max_key_size;
                    let max_value_size = derived_page_size.max_value_size;

                    assert!(
                        K::BOUND.max_size() <= max_key_size,
                        "max_key_size must be <= {max_key_size}",
                    );

                    assert!(
                        V::BOUND.max_size() <= max_value_size,
                        "max_value_size must be <= {max_value_size}"
                    );

                    Version::V1(derived_page_size)
                }
            }
            other => other,
        };

        let allocator_addr = Address::from(ALLOCATOR_OFFSET as u64);
        Self {
            root_addr: header.root_addr,
            allocator: Allocator::load(memory, allocator_addr),
            version,
            length: header.length,
            cache: RefCell::new(NodeCache::new(
                version.page_size().get(),
                DEFAULT_NODE_CACHE_NUM_SLOTS,
            )),
            _phantom: PhantomData,
        }
    }

    /// Reads the header from the specified memory.
    fn read_header(memory: &M) -> BTreeHeader {
        // Read the header
        let mut buf = [0; PACKED_HEADER_SIZE];
        memory.read(0, &mut buf);

        assert_eq!(&buf[0..3], MAGIC, "Bad magic.");

        match buf[3] {
            LAYOUT_VERSION => {
                // Deserialize the fields
                BTreeHeader {
                    version: Version::V1(DerivedPageSize {
                        max_key_size: u32::from_le_bytes(buf[4..8].try_into().unwrap()),
                        max_value_size: u32::from_le_bytes(buf[8..12].try_into().unwrap()),
                    }),
                    root_addr: Address::from(u64::from_le_bytes(buf[12..20].try_into().unwrap())),
                    length: u64::from_le_bytes(buf[20..28].try_into().unwrap()),
                }
            }
            LAYOUT_VERSION_2 => {
                // Load the page size.
                let page_size = {
                    // Page sizes can be stored either as a direct value or as max/value sizes.
                    let a = u32::from_le_bytes(buf[4..8].try_into().unwrap());
                    let b = u32::from_le_bytes(buf[8..12].try_into().unwrap());

                    if b == PAGE_SIZE_VALUE_MARKER {
                        // Page size is stored as a direct value
                        PageSize::Value(a)
                    } else {
                        // Page size is stored as a derived value.
                        PageSize::Derived(DerivedPageSize {
                            max_key_size: a,
                            max_value_size: b,
                        })
                    }
                };

                // Deserialize the fields
                BTreeHeader {
                    version: Version::V2(page_size),
                    root_addr: Address::from(u64::from_le_bytes(buf[12..20].try_into().unwrap())),
                    length: u64::from_le_bytes(buf[20..28].try_into().unwrap()),
                }
            }
            version => {
                panic!("Unsupported version: {version}.");
            }
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// The previous value of the key, if present, is returned.
    ///
    /// PRECONDITION:
    ///   key.to_bytes().len() <= max_size(Key)
    ///   value.to_bytes().len() <= max_size(Value)
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let value = value.into_bytes_checked();

        let root = if self.root_addr == NULL {
            // No root present. Allocate one.
            let node = self.allocate_node(NodeType::Leaf);
            self.root_addr = node.address();
            self.save_header();
            node
        } else {
            // Load the root from memory.
            let mut root = self.take_or_load_node(self.root_addr);

            // Check if the key already exists in the root.
            if let Ok(idx) = root.search(&key, self.memory()) {
                // Key found, replace its value and return the old one.
                return Some(V::from_bytes(Cow::Owned(
                    self.update_value(&mut root, idx, value),
                )));
            }

            // If the root is full, we need to introduce a new node as the root.
            //
            // NOTE: In the case where we are overwriting an existing key, then introducing
            // a new root node isn't strictly necessary. However, that's a micro-optimization
            // that adds more complexity than it's worth.
            if root.is_full() {
                // The root is full. Allocate a new node that will be used as the new root.
                let mut new_root = self.allocate_node(NodeType::Internal);

                // The new root has the old root as its only child.
                new_root.push_child(self.root_addr);

                // Update the root address.
                self.root_addr = new_root.address();
                self.save_header();

                // Split the old (full) root.
                self.split_child(&mut new_root, 0, None);

                new_root
            } else {
                root
            }
        };

        self.insert_nonfull(root, key, value, 0)
            .map(Cow::Owned)
            .map(V::from_bytes)
    }

    /// Inserts an entry into a node that is *not full*.
    fn insert_nonfull(
        &mut self,
        mut node: Node<K>,
        key: K,
        value: Vec<u8>,
        depth: u8,
    ) -> Option<Vec<u8>> {
        // We're guaranteed by the caller that the provided node is not full.
        assert!(!node.is_full());

        // Look for the key in the node.
        match node.search(&key, self.memory()) {
            Ok(idx) => {
                // Key found, replace its value and return the old one.
                Some(self.update_value(&mut node, idx, value))
            }
            Err(idx) => {
                // The key isn't in the node. `idx` is where that key should be inserted.

                match node.node_type() {
                    NodeType::Leaf => {
                        // The node is a non-full leaf.
                        // Insert the entry at the proper location.
                        node.insert_entry(idx, (key, value));
                        self.save_node(&mut node);

                        // Update the length.
                        self.length += 1;
                        self.save_header();

                        // No previous value to return.
                        None
                    }
                    NodeType::Internal => {
                        // The node is an internal node.
                        // Load the child that we should add the entry to.
                        let mut child = self.take_or_load_node(node.child(idx));
                        let child_depth = depth.saturating_add(1);

                        if child.is_full() {
                            // Check if the key already exists in the child.
                            if let Ok(idx) = child.search(&key, self.memory()) {
                                // Key found, replace its value and return the old one.
                                // The parent node is unmodified — return it to cache.
                                self.return_node(node, depth);
                                return Some(self.update_value(&mut child, idx, value));
                            }

                            // The child is full. Split the child.
                            // Pass the already-loaded child to avoid a redundant load.
                            self.split_child(&mut node, idx, Some(child));

                            // The children have now changed. Search again for
                            // the child where we need to store the entry in.
                            let idx = node.search(&key, self.memory()).unwrap_or_else(|idx| idx);
                            child = self.load_node(node.child(idx));
                            // split_child saved node to memory; return the
                            // up-to-date in-memory copy to the cache.
                            self.return_node(node, depth);
                        } else {
                            // Happy path: child is not full. The current node
                            // will not be modified — return it to cache.
                            self.return_node(node, depth);
                        }

                        // The child should now be not full.
                        assert!(!child.is_full());

                        self.insert_nonfull(child, key, value, child_depth)
                    }
                }
            }
        }
    }

    /// Takes as input a nonfull internal `node` and index to its full child, then
    /// splits this child into two, adding an additional child to `node`.
    ///
    /// Example:
    /// ```ignore
    ///                          [ ... M   Y ... ]
    ///                                  |
    ///                 [ N  O  P  Q  R  S  T  U  V  W  X ]
    /// ```
    ///
    /// After splitting becomes:
    /// ```ignore
    ///                         [ ... M  S  Y ... ]
    ///                                 / \
    ///                [ N  O  P  Q  R ]   [ T  U  V  W  X ]
    /// ```
    ///
    fn split_child(
        &mut self,
        node: &mut Node<K>,
        full_child_idx: usize,
        full_child: Option<Node<K>>,
    ) {
        // The node must not be full.
        assert!(!node.is_full());

        // Use the pre-loaded child if provided, otherwise load from memory.
        let mut full_child =
            full_child.unwrap_or_else(|| self.load_node(node.child(full_child_idx)));
        assert!(full_child.is_full());

        // Create a sibling to this full child (which has to be the same type).
        let mut sibling = self.allocate_node(full_child.node_type());
        assert_eq!(sibling.node_type(), full_child.node_type());

        // Add sibling as a new child in the node.
        node.insert_child(full_child_idx + 1, sibling.address());

        let (median_key, median_value) = full_child.split(&mut sibling, self.memory());

        node.insert_entry(full_child_idx, (median_key, median_value));

        self.save_node(&mut sibling);
        self.save_node(&mut full_child);
        self.save_node(node);
    }

    /// Returns the value for the given key, if it exists.
    pub fn get(&self, key: &K) -> Option<V> {
        if self.root_addr == NULL {
            return None;
        }
        self.traverse(self.root_addr, 0, key, |node, idx| {
            node.read_value_uncached(idx, self.memory())
        })
        .map(Cow::Owned)
        .map(V::from_bytes)
    }

    /// Returns true if the key exists.
    pub fn contains_key(&self, key: &K) -> bool {
        // An empty closure returns Some(()) if the key is found.
        self.root_addr != NULL && self.traverse(self.root_addr, 0, key, |_, _| ()).is_some()
    }

    /// Recursively traverses from `node_addr`, invoking `f` if `key` is found. Stops at a leaf if not.
    ///
    /// Uses the node cache: nodes are taken out before use and returned after.
    /// `depth` is the distance from the root (root = 0).
    fn traverse<F, R>(&self, node_addr: Address, depth: u8, key: &K, f: F) -> Option<R>
    where
        F: Fn(&Node<K>, usize) -> R,
    {
        let node = self.take_or_load_node(node_addr);
        match node.search(key, self.memory()) {
            Ok(idx) => {
                let result = f(&node, idx); // Key found: apply `f`.
                self.return_node(node, depth);
                Some(result)
            }
            Err(idx) => match node.node_type() {
                NodeType::Leaf => {
                    self.return_node(node, depth);
                    None // At a leaf: key not present.
                }
                NodeType::Internal => {
                    let child_addr = node.child(idx);
                    self.return_node(node, depth);
                    self.traverse(child_addr, depth.saturating_add(1), key, f)
                }
            },
        }
    }

    /// A helper function to find either the first or last entry in the tree, depending on the `is_first` flag.
    fn find_first_or_last<R, F>(&self, node: &Node<K>, is_first: bool, depth: u8, extract: F) -> R
    where
        F: Fn(&Node<K>, usize, &M) -> R,
    {
        match node.node_type() {
            NodeType::Leaf => {
                let idx = if is_first {
                    0
                } else {
                    // Last entry index in a 0-based array of entries.
                    node.num_entries() - 1
                };
                extract(node, idx, self.memory())
            }
            NodeType::Internal => {
                let child_addr = if is_first {
                    node.child(0)
                } else {
                    // Last child index in a 0-based array of children.
                    node.child(node.children_len() - 1)
                };
                let child = self.take_or_load_node(child_addr);
                let new_depth = depth.saturating_add(1);
                let result = self.find_first_or_last(&child, is_first, new_depth, extract);
                self.return_node(child, new_depth);
                result
            }
        }
    }

    #[inline(always)]
    fn first_entry_inner(&self, node: &Node<K>, depth: u8) -> Entry<K> {
        self.find_first_or_last(node, true, depth, |n, i, m| {
            n.get_key_read_value_uncached(i, m)
        })
    }

    #[inline(always)]
    fn last_entry_inner(&self, node: &Node<K>, depth: u8) -> Entry<K> {
        self.find_first_or_last(node, false, depth, |n, i, m| {
            n.get_key_read_value_uncached(i, m)
        })
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> u64 {
        self.length
    }

    /// Returns the underlying memory.
    pub fn into_memory(self) -> M {
        self.allocator.into_memory()
    }

    /// Removes all elements from the map.
    #[deprecated(since = "0.6.3", note = "please use `clear_new` instead")]
    // TODO: In next major release (v1.0), remove this deprecated method and rename
    // `clear_new` to `clear` for consistency with standard Rust collections.
    pub fn clear(self) -> Self {
        let mem = self.allocator.into_memory();
        Self::new(mem)
    }

    /// Removes all elements from the map.
    // TODO: In next major release (v1.0), rename this method to `clear` to follow
    // standard Rust collection naming conventions.
    pub fn clear_new(&mut self) {
        self.root_addr = NULL;
        self.length = 0;
        self.allocator.clear();
        let num_slots = self.cache.get_mut().num_slots();
        *self.cache.get_mut() = NodeCache::new(self.version.page_size().get(), num_slots);
        self.save_header();
    }

    /// Returns the first key-value pair in the map. The key in this
    /// pair is the minimum key in the map.
    pub fn first_key_value(&self) -> Option<(K, V)> {
        if self.root_addr == NULL {
            return None;
        }
        let root = self.take_or_load_node(self.root_addr);
        let (k, encoded_v) = self.first_entry_inner(&root, 0);
        self.return_node(root, 0);
        Some((k, V::from_bytes(Cow::Owned(encoded_v))))
    }

    /// Returns the last key-value pair in the map. The key in this
    /// pair is the maximum key in the map.
    pub fn last_key_value(&self) -> Option<(K, V)> {
        if self.root_addr == NULL {
            return None;
        }
        let root = self.take_or_load_node(self.root_addr);
        let (k, encoded_v) = self.last_entry_inner(&root, 0);
        self.return_node(root, 0);
        Some((k, V::from_bytes(Cow::Owned(encoded_v))))
    }

    fn memory(&self) -> &M {
        self.allocator.memory()
    }

    fn allocator_mut(&mut self) -> &mut Allocator<M> {
        &mut self.allocator
    }

    /// Removes a key from the map, returning the previous value at the key if it exists.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if self.root_addr == NULL {
            return None;
        }

        let root_node = self.take_or_load_node(self.root_addr);
        self.remove_helper(root_node, key, 0)
            .map(Cow::Owned)
            .map(V::from_bytes)
    }

    /// Removes and returns the last element in the map. The key of this element is the maximum key that was in the map
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        if self.root_addr == NULL {
            return None;
        }

        let root = self.take_or_load_node(self.root_addr);
        self.remove_rightmost(root, 0)
            .map(|(k, v)| (k, V::from_bytes(Cow::Owned(v))))
    }

    /// Removes and returns the first element in the map. The key of this element is the minimum key that was in the map
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        if self.root_addr == NULL {
            return None;
        }

        let root = self.take_or_load_node(self.root_addr);
        self.remove_leftmost(root, 0)
            .map(|(k, v)| (k, V::from_bytes(Cow::Owned(v))))
    }

    /// A helper method for recursively removing a key from the B-tree.
    fn remove_helper(&mut self, mut node: Node<K>, key: &K, depth: u8) -> Option<Vec<u8>> {
        if node.address() != self.root_addr {
            // We're guaranteed that whenever this method is called an entry can be
            // removed from the node without it needing to be merged into a sibling.
            // This strengthened condition allows us to delete an entry in a single
            // pass most of the time without having to back up.
            assert!(node.can_remove_entry_without_merging());
        }

        match node.node_type() {
            NodeType::Leaf => {
                match node.search(key, self.memory()) {
                    Ok(idx) => {
                        // Case 1: The node is a leaf node and the key exists in it.
                        // This is the simplest case. The key is removed from the leaf.
                        let value = node.remove_entry(idx, self.memory()).1;
                        self.length -= 1;

                        if node.entries_len() == 0 {
                            assert_eq!(
                                node.address(), self.root_addr,
                                "Removal can only result in an empty leaf node if that node is the root"
                            );

                            // Deallocate the empty node.
                            self.deallocate_node(node);
                            self.root_addr = NULL;
                        } else {
                            self.save_node(&mut node);
                        }

                        self.save_header();
                        Some(value)
                    }
                    _ => {
                        // Key not found. Return the unmodified node to cache.
                        self.return_node(node, depth);
                        None
                    }
                }
            }
            NodeType::Internal => {
                match node.search(key, self.memory()) {
                    Ok(idx) => {
                        // Case 2: The node is an internal node and the key exists in it.

                        let left_child = self.take_or_load_node(node.child(idx));
                        if left_child.can_remove_entry_without_merging() {
                            // Case 2.a: A key can be removed from the left child without merging.
                            //
                            //                       parent
                            //                  [..., key, ...]
                            //                       /   \
                            //            [left child]   [...]
                            //           /            \
                            //        [...]         [..., key predecessor]
                            //
                            // In this case, we replace `key` with the key's predecessor from the
                            // left child's subtree, then we recursively delete the key's
                            // predecessor for the following end result:
                            //
                            //                       parent
                            //            [..., key predecessor, ...]
                            //                       /   \
                            //            [left child]   [...]
                            //           /            \
                            //        [...]          [...]

                            // Remove the predecessor in a single pass (no double traversal).
                            let predecessor =
                                self.remove_rightmost(left_child, depth.saturating_add(1))?;

                            // Replace the `key` with its predecessor.
                            let (_, old_value) = node.swap_entry(idx, predecessor, self.memory());

                            // Save the parent node.
                            self.save_node(&mut node);
                            return Some(old_value);
                        }

                        let right_child = self.take_or_load_node(node.child(idx + 1));
                        if right_child.can_remove_entry_without_merging() {
                            // Case 2.b: A key can be removed from the right child without merging.
                            //
                            //                       parent
                            //                  [..., key, ...]
                            //                       /   \
                            //                   [...]   [right child]
                            //                          /             \
                            //              [key successor, ...]     [...]
                            //
                            // In this case, we replace `key` with the key's successor from the
                            // right child's subtree, then we recursively delete the key's
                            // successor for the following end result:
                            //
                            //                       parent
                            //            [..., key successor, ...]
                            //                       /   \
                            //                  [...]   [right child]
                            //                           /            \
                            //                        [...]          [...]

                            // Return the unmodified left child to the cache.
                            self.return_node(left_child, depth.saturating_add(1));

                            // Remove the successor in a single pass (no double traversal).
                            let successor =
                                self.remove_leftmost(right_child, depth.saturating_add(1))?;

                            // Replace the `key` with its successor.
                            let (_, old_value) = node.swap_entry(idx, successor, self.memory());

                            // Save the parent node.
                            self.save_node(&mut node);
                            return Some(old_value);
                        }

                        // Case 2.c: Both the left and right child are at their minimum sizes.
                        //
                        //                       parent
                        //                  [..., key, ...]
                        //                       /   \
                        //            [left child]   [right child]
                        //
                        // In this case, we merge (left child, key, right child) into a single
                        // node. The result will look like this:
                        //
                        //                       parent
                        //                     [...  ...]
                        //                         |
                        //          [left child, `key`, right child] <= new child
                        //
                        // We then recurse on this new child to delete `key`.
                        //
                        // If `parent` becomes empty (which can only happen if it's the root),
                        // then `parent` is deleted and `new_child` becomes the new root.
                        assert!(left_child.at_minimum());
                        assert!(right_child.at_minimum());

                        // Merge the right child into the left child.
                        let mut new_child = self.merge(
                            right_child,
                            left_child,
                            node.remove_entry(idx, self.memory()),
                        );

                        // Remove the right child from the parent node.
                        node.remove_child(idx + 1);

                        if node.entries_len() == 0 {
                            // Can only happen if this node is root.
                            assert_eq!(node.address(), self.root_addr);
                            assert_eq!(node.child(0), new_child.address());
                            assert_eq!(node.children_len(), 1);

                            self.root_addr = new_child.address();

                            // Deallocate the root node.
                            self.deallocate_node(node);
                            self.save_header();
                        } else {
                            self.save_node(&mut node);
                        }

                        self.save_node(&mut new_child);

                        // Recursively delete the key.
                        self.remove_helper(new_child, key, depth.saturating_add(1))
                    }
                    Err(idx) => {
                        // Case 3: The node is an internal node and the key does NOT exist in it.

                        // If the key does exist in the tree, it will exist in the subtree at index
                        // `idx`.
                        let mut child = self.take_or_load_node(node.child(idx));
                        let child_depth = depth.saturating_add(1);

                        if child.can_remove_entry_without_merging() {
                            // The child has enough nodes. Recurse to delete the `key` from the
                            // `child`.
                            // The current node is not modified — return it to cache.
                            self.return_node(node, depth);
                            return self.remove_helper(child, key, child_depth);
                        }

                        // An entry can't be removed from the child without merging.
                        // See if it has a sibling where an entry can be removed without merging.
                        // Siblings are loaded without cache: all rebalancing paths modify
                        // and save every loaded node, so caching them would be wasted.
                        let mut left_sibling = if idx > 0 {
                            Some(self.load_node(node.child(idx - 1)))
                        } else {
                            None
                        };

                        let mut right_sibling = if idx + 1 < node.children_len() {
                            Some(self.load_node(node.child(idx + 1)))
                        } else {
                            None
                        };

                        if let Some(ref mut left_sibling) = left_sibling {
                            if left_sibling.can_remove_entry_without_merging() {
                                // Case 3.a (left):
                                // A key can be removed from the left child without merging.
                                //
                                //                            [d] (parent)
                                //                           /   \
                                //  (left sibling) [a, b, c]     [e, f] (child)
                                //                         \
                                //                         [c']
                                //
                                // In this case, we move a key down from the parent into the child
                                // and move a key from the left sibling up into the parent
                                // resulting in the following tree:
                                //
                                //                            [c] (parent)
                                //                           /   \
                                //       (left sibling) [a, b]   [d, e, f] (child)
                                //                              /
                                //                            [c']
                                //
                                // We then recurse to delete the key from the child.

                                // Remove the last entry from the left sibling.
                                let (left_sibling_key, left_sibling_value) =
                                    left_sibling.pop_entry(self.memory()).unwrap();

                                // Replace the parent's entry with the one from the left sibling.
                                let (parent_key, parent_value) = node.swap_entry(
                                    idx - 1,
                                    (left_sibling_key, left_sibling_value),
                                    self.memory(),
                                );

                                // Move the entry from the parent into the child.
                                child.insert_entry(0, (parent_key, parent_value));

                                // Move the last child from left sibling into child.
                                if let Some(last_child) = left_sibling.pop_child() {
                                    assert_eq!(left_sibling.node_type(), NodeType::Internal);
                                    assert_eq!(child.node_type(), NodeType::Internal);

                                    child.insert_child(0, last_child);
                                } else {
                                    assert_eq!(left_sibling.node_type(), NodeType::Leaf);
                                    assert_eq!(child.node_type(), NodeType::Leaf);
                                }

                                self.save_node(left_sibling);
                                self.save_node(&mut child);
                                self.save_node(&mut node);
                                return self.remove_helper(child, key, child_depth);
                            }
                        }

                        if let Some(right_sibling) = &mut right_sibling {
                            if right_sibling.can_remove_entry_without_merging() {
                                // Case 3.a (right):
                                // A key can be removed from the right child without merging.
                                //
                                //                            [c] (parent)
                                //                           /   \
                                //             (child) [a, b]     [d, e, f] (right sibling)
                                //                               /
                                //                            [d']
                                //
                                // In this case, we move a key down from the parent into the child
                                // and move a key from the right sibling up into the parent
                                // resulting in the following tree:
                                //
                                //                            [d] (parent)
                                //                           /   \
                                //          (child) [a, b, c]     [e, f] (right sibling)
                                //                          \
                                //                           [d']
                                //
                                // We then recurse to delete the key from the child.

                                // Remove the first entry from the right sibling.
                                let (right_sibling_key, right_sibling_value) =
                                    right_sibling.remove_entry(0, self.memory());

                                // Replace the parent's entry with the one from the right sibling.
                                let parent_entry = node.swap_entry(
                                    idx,
                                    (right_sibling_key, right_sibling_value),
                                    self.memory(),
                                );

                                // Move the entry from the parent into the child.
                                child.push_entry(parent_entry);

                                // Move the first child of right_sibling into `child`.
                                match right_sibling.node_type() {
                                    NodeType::Internal => {
                                        assert_eq!(child.node_type(), NodeType::Internal);
                                        child.push_child(right_sibling.remove_child(0));
                                    }
                                    NodeType::Leaf => {
                                        assert_eq!(child.node_type(), NodeType::Leaf);
                                    }
                                }

                                self.save_node(right_sibling);
                                self.save_node(&mut child);
                                self.save_node(&mut node);
                                return self.remove_helper(child, key, child_depth);
                            }
                        }

                        // Case 3.b: Both the left and right siblings are at their minimum sizes.

                        if let Some(left_sibling) = left_sibling {
                            // Merge child into left sibling if it exists.

                            assert!(left_sibling.at_minimum());
                            let left_sibling = self.merge(
                                child,
                                left_sibling,
                                node.remove_entry(idx - 1, self.memory()),
                            );
                            // Removing child from parent.
                            node.remove_child(idx);

                            if node.entries_len() == 0 {
                                let node_address = node.address();
                                self.deallocate_node(node);

                                if node_address == self.root_addr {
                                    // Update the root.
                                    self.root_addr = left_sibling.address();
                                    self.save_header();
                                }
                            } else {
                                self.save_node(&mut node);
                            }

                            return self.remove_helper(left_sibling, key, child_depth);
                        }

                        if let Some(right_sibling) = right_sibling {
                            // Merge child into right sibling.

                            assert!(right_sibling.at_minimum());
                            let right_sibling = self.merge(
                                child,
                                right_sibling,
                                node.remove_entry(idx, self.memory()),
                            );

                            // Removing child from parent.
                            node.remove_child(idx);

                            if node.entries_len() == 0 {
                                let node_address = node.address();
                                self.deallocate_node(node);

                                if node_address == self.root_addr {
                                    // Update the root.
                                    self.root_addr = right_sibling.address();
                                    self.save_header();
                                }
                            } else {
                                self.save_node(&mut node);
                            }

                            return self.remove_helper(right_sibling, key, child_depth);
                        }

                        unreachable!("At least one of the siblings must exist.");
                    }
                }
            }
        }
    }

    /// Removes and returns the rightmost (maximum) entry in the subtree rooted
    /// at `node`, in a single top-down pass. This avoids the double traversal
    /// of the previous approach (get_max + remove_helper).
    fn remove_rightmost(&mut self, mut node: Node<K>, depth: u8) -> Option<Entry<K>> {
        match node.node_type() {
            NodeType::Leaf => {
                let entry = node.pop_entry(self.memory())?;
                self.length -= 1;

                if node.entries_len() == 0 {
                    assert_eq!(node.address(), self.root_addr);
                    self.deallocate_node(node);
                    self.root_addr = NULL;
                } else {
                    self.save_node(&mut node);
                }
                self.save_header();
                Some(entry)
            }
            NodeType::Internal => {
                let last_idx = node.children_len() - 1;
                let child_depth = depth.saturating_add(1);
                let child = self.take_or_load_node(node.child(last_idx));

                if child.can_remove_entry_without_merging() {
                    // The current node is not modified — return it to cache.
                    self.return_node(node, depth);
                    return self.remove_rightmost(child, child_depth);
                }

                // The rightmost child is at minimum. Steal from its left sibling or merge.
                // Siblings are loaded without cache: all rebalancing paths modify
                // and save every loaded node, so caching them would be wasted.
                let left_sibling_idx = last_idx - 1;
                let mut left_sibling = self.load_node(node.child(left_sibling_idx));

                if left_sibling.can_remove_entry_without_merging() {
                    // Rotate right: left_sibling -> parent -> child
                    let mut child = child;
                    let (left_key, left_value) = left_sibling.pop_entry(self.memory()).unwrap();
                    let (parent_key, parent_value) =
                        node.swap_entry(last_idx - 1, (left_key, left_value), self.memory());
                    child.insert_entry(0, (parent_key, parent_value));

                    if let Some(last_child) = left_sibling.pop_child() {
                        child.insert_child(0, last_child);
                    }

                    self.save_node(&mut left_sibling);
                    self.save_node(&mut child);
                    self.save_node(&mut node);
                    return self.remove_rightmost(child, child_depth);
                }

                // Both at minimum: merge child into left sibling.
                let merged = self.merge(
                    child,
                    left_sibling,
                    node.remove_entry(last_idx - 1, self.memory()),
                );
                node.remove_child(last_idx);

                if node.entries_len() == 0 {
                    assert_eq!(node.address(), self.root_addr);
                    self.root_addr = merged.address();
                    self.deallocate_node(node);
                    self.save_header();
                } else {
                    self.save_node(&mut node);
                }

                self.remove_rightmost(merged, child_depth)
            }
        }
    }

    /// Removes and returns the leftmost (minimum) entry in the subtree rooted
    /// at `node`, in a single top-down pass.
    fn remove_leftmost(&mut self, mut node: Node<K>, depth: u8) -> Option<Entry<K>> {
        match node.node_type() {
            NodeType::Leaf => {
                if node.entries_len() == 0 {
                    return None;
                }
                let entry = node.remove_entry(0, self.memory());
                self.length -= 1;

                if node.entries_len() == 0 {
                    assert_eq!(node.address(), self.root_addr);
                    self.deallocate_node(node);
                    self.root_addr = NULL;
                } else {
                    self.save_node(&mut node);
                }
                self.save_header();
                Some(entry)
            }
            NodeType::Internal => {
                let child_depth = depth.saturating_add(1);
                let child = self.take_or_load_node(node.child(0));

                if child.can_remove_entry_without_merging() {
                    // The current node is not modified — return it to cache.
                    self.return_node(node, depth);
                    return self.remove_leftmost(child, child_depth);
                }

                // The leftmost child is at minimum. Steal from its right sibling or merge.
                // Siblings are loaded without cache: all rebalancing paths modify
                // and save every loaded node, so caching them would be wasted.
                let mut right_sibling = self.load_node(node.child(1));

                if right_sibling.can_remove_entry_without_merging() {
                    // Rotate left: right_sibling -> parent -> child
                    let mut child = child;
                    let (right_key, right_value) = right_sibling.remove_entry(0, self.memory());
                    let parent_entry = node.swap_entry(0, (right_key, right_value), self.memory());
                    child.push_entry(parent_entry);

                    if right_sibling.node_type() == NodeType::Internal {
                        child.push_child(right_sibling.remove_child(0));
                    }

                    self.save_node(&mut right_sibling);
                    self.save_node(&mut child);
                    self.save_node(&mut node);
                    return self.remove_leftmost(child, child_depth);
                }

                // Both at minimum: merge child into right sibling.
                let merged = self.merge(child, right_sibling, node.remove_entry(0, self.memory()));
                node.remove_child(0);

                if node.entries_len() == 0 {
                    assert_eq!(node.address(), self.root_addr);
                    self.root_addr = merged.address();
                    self.deallocate_node(node);
                    self.save_header();
                } else {
                    self.save_node(&mut node);
                }

                self.remove_leftmost(merged, child_depth)
            }
        }
    }

    /// Returns an iterator over the entries of the map, sorted by key.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    /// let mut map: BTreeMap<u64, String, _> = BTreeMap::init(DefaultMemoryImpl::default());
    ///
    /// map.insert(1, "one".to_string());
    /// map.insert(2, "two".to_string());
    ///
    /// for entry in map.iter() {
    ///     println!("{}: {}", entry.key(), entry.value());
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V, M> {
        self.iter_internal().into()
    }

    /// Returns an iterator over the entries in the map where keys
    /// belong to the specified range.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ic_stable_structures::{BTreeMap, DefaultMemoryImpl};
    /// use std::ops::Bound;
    ///
    /// let mut map: BTreeMap<u64, String, _> = BTreeMap::init(DefaultMemoryImpl::default());
    /// map.insert(1, "one".to_string());
    /// map.insert(2, "two".to_string());
    /// map.insert(3, "three".to_string());
    ///
    /// // Get entries with keys between 1 and 3 (inclusive)
    /// for entry in map.range((Bound::Included(1), Bound::Included(3))) {
    ///     println!("{}: {}", entry.key(), entry.value());
    /// }
    /// ```
    pub fn range(&self, key_range: impl RangeBounds<K>) -> Iter<'_, K, V, M> {
        self.range_internal(key_range).into()
    }

    /// Returns an iterator starting just before the given key.
    ///
    /// Finds the largest key strictly less than `bound` and starts from it.
    /// Useful when `range(bound..)` skips the previous element.
    ///
    /// Returns an empty iterator if no smaller key exists.
    pub fn iter_from_prev_key(&self, bound: &K) -> Iter<'_, K, V, M> {
        if let Some(entry) = self.range(..bound).next_back() {
            let start_key = entry.key().clone();
            IterInternal::new_in_range(self, (Bound::Included(start_key), Bound::Unbounded)).into()
        } else {
            IterInternal::null(self).into()
        }
    }

    /// **Deprecated**: use `iter_from_prev_key` instead.
    ///
    /// The name `iter_upper_bound` was misleading — it suggested an inclusive
    /// upper bound. In reality, it starts from the largest key strictly less
    /// than the given bound.
    ///
    /// The new name, `iter_from_prev_key`, better reflects this behavior and
    /// improves code clarity.
    #[deprecated(note = "use `iter_from_prev_key` instead")]
    // TODO: In next major release (v1.0), remove this deprecated method to clean up the API.
    pub fn iter_upper_bound(&self, bound: &K) -> Iter<'_, K, V, M> {
        self.iter_from_prev_key(bound)
    }

    /// Returns an iterator over the keys of the map.
    pub fn keys(&self) -> KeysIter<'_, K, V, M> {
        self.iter_internal().into()
    }

    /// Returns an iterator over the keys of the map which belong to the specified range.
    pub fn keys_range(&self, key_range: impl RangeBounds<K>) -> KeysIter<'_, K, V, M> {
        self.range_internal(key_range).into()
    }

    /// Returns an iterator over the values of the map, sorted by key.
    pub fn values(&self) -> ValuesIter<'_, K, V, M> {
        self.iter_internal().into()
    }

    /// Returns an iterator over the values of the map where keys
    /// belong to the specified range.
    pub fn values_range(&self, key_range: impl RangeBounds<K>) -> ValuesIter<'_, K, V, M> {
        self.range_internal(key_range).into()
    }

    fn iter_internal(&self) -> IterInternal<'_, K, V, M> {
        IterInternal::new(self)
    }

    fn range_internal(&self, key_range: impl RangeBounds<K>) -> IterInternal<'_, K, V, M> {
        if self.root_addr == NULL {
            // Map is empty.
            return IterInternal::null(self);
        }

        let range = (
            key_range.start_bound().cloned(),
            key_range.end_bound().cloned(),
        );

        IterInternal::new_in_range(self, range)
    }

    /// Merges one node (`source`) into another (`into`), along with a median entry.
    ///
    /// Example (values are not included for brevity):
    ///
    /// Input:
    ///   Source: [1, 2, 3]
    ///   Into: [5, 6, 7]
    ///   Median: 4
    ///
    /// Output:
    ///   [1, 2, 3, 4, 5, 6, 7] (stored in the `into` node)
    ///   `source` is deallocated.
    fn merge(&mut self, source: Node<K>, mut into: Node<K>, median: Entry<K>) -> Node<K> {
        let source_addr = source.address();
        into.merge(source, median, &mut self.allocator);
        // Node::merge saves `into` and deallocates `source` directly through
        // the allocator, so we must invalidate both cache slots here.
        let cache = self.cache.get_mut();
        cache.invalidate(into.address());
        cache.invalidate(source_addr);
        into
    }

    /// Allocates a new node of the given type.
    fn allocate_node(&mut self, node_type: NodeType) -> Node<K> {
        match self.version {
            Version::V1(page_size) => Node::new_v1(self.allocator.allocate(), node_type, page_size),
            Version::V2(page_size) => Node::new_v2(self.allocator.allocate(), node_type, page_size),
        }
    }

    /// Deallocates a node and invalidates its cache slot.
    #[inline]
    fn deallocate_node(&mut self, node: Node<K>) {
        let addr = node.address();
        node.deallocate(self.allocator_mut());
        self.cache.get_mut().invalidate(addr);
    }

    /// Takes a node from the cache, or loads it from memory if not cached.
    ///
    /// Used by read paths (`&self`). The caller must call `return_node` when
    /// done to put the node back into the cache.
    #[inline(always)]
    fn take_or_load_node(&self, address: Address) -> Node<K> {
        if let Some(node) = self.cache.borrow_mut().take(address) {
            return node;
        }
        Node::load(address, self.version.page_size(), self.memory())
    }

    /// Returns a node to the cache after use on a read path.
    ///
    /// `depth` is the distance from the root (root = 0), used by the
    /// cache eviction policy.
    #[inline(always)]
    fn return_node(&self, node: Node<K>, depth: u8) {
        self.cache.borrow_mut().put(node.address(), node, depth);
    }

    /// Loads a node from memory, bypassing the cache.
    #[inline]
    fn load_node(&self, address: Address) -> Node<K> {
        Node::load(address, self.version.page_size(), self.memory())
    }

    /// Saves the node to memory and invalidates the cache slot.
    // TODO: benchmark putting the node back into the cache after saving
    // instead of invalidating, so subsequent reads (especially of the root
    // and depth-1 nodes) hit the cache. Requires cloning or taking ownership.
    #[inline]
    fn save_node(&mut self, node: &mut Node<K>) {
        node.save(self.allocator_mut());
        self.cache.get_mut().invalidate(node.address());
    }

    /// Replaces the value at `idx` in the node, saves the node, and returns the old value.
    fn update_value(&mut self, node: &mut Node<K>, idx: usize, new_value: Vec<u8>) -> Vec<u8> {
        let old_value = node.swap_value(idx, new_value, self.memory());
        self.save_node(node);
        old_value
    }

    /// Saves the map to memory.
    fn save_header(&self) {
        let header = BTreeHeader {
            version: self.version,
            root_addr: self.root_addr,
            length: self.length,
        };

        Self::write_header(&header, self.memory());
    }

    /// Write the layout header to the memory.
    fn write_header(header: &BTreeHeader, memory: &M) {
        // Serialize the header
        let mut buf = [0; PACKED_HEADER_SIZE];
        buf[0..3].copy_from_slice(MAGIC.as_slice());
        match header.version {
            Version::V1(DerivedPageSize {
                max_key_size,
                max_value_size,
            })
            | Version::V2(PageSize::Derived(DerivedPageSize {
                max_key_size,
                max_value_size,
            })) => {
                buf[3] = LAYOUT_VERSION;
                buf[4..8].copy_from_slice(&max_key_size.to_le_bytes());
                buf[8..12].copy_from_slice(&max_value_size.to_le_bytes());
            }
            Version::V2(PageSize::Value(page_size)) => {
                buf[3] = LAYOUT_VERSION_2;
                buf[4..8].copy_from_slice(&page_size.to_le_bytes());
                buf[8..12].copy_from_slice(&PAGE_SIZE_VALUE_MARKER.to_le_bytes());
            }
        };
        buf[12..20].copy_from_slice(&header.root_addr.get().to_le_bytes());
        buf[20..28].copy_from_slice(&header.length.to_le_bytes());
        // Write the header
        crate::write(memory, 0, &buf);
    }
}

#[cfg(test)]
mod tests;
