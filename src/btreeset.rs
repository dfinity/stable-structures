//! This module implements a key store based on a B-Tree
//! in stable memory.
//!
//! # V1 layout
//!
//! ```text
//! ---------------------------------------- <- Address 0
//! Magic "BTS"                 ↕ 3 bytes
//! ----------------------------------------
//! Layout version              ↕ 1 byte
//! ----------------------------------------
//! Max key size                ↕ 4 bytes     OR    Page size                   ↕ 4 bytes
//! ----------------------------------------      ----------------------------------------
//! Root node address           ↕ 8 bytes
//! ----------------------------------------
//! Length (number of elements) ↕ 8 bytes
//! ---------------------------------------- <- Address 24 (PACKED_HEADER_SIZE)
//! Reserved space              ↕ 24 bytes
//! ---------------------------------------- <- Address 48 (ALLOCATOR_OFFSET)
//! Allocator
//! ----------------------------------------
//! ... free memory for nodes
//! ----------------------------------------
//! ```

#[cfg(test)]
mod proptests;

const MAGIC: &[u8; 3] = b"BTS";
const LAYOUT_VERSION: u8 = 1;
// The sum of all the header fields, i.e. size of a packed header.
const PACKED_HEADER_SIZE: usize = 24;
// The offset where the allocator begins.
const ALLOCATOR_OFFSET: usize = 48;

// The default page size to use in BTreeMap V2 in bytes.
const DEFAULT_PAGE_SIZE: u32 = 1024;

// A marker to indicate that the `PageSize` stored in the header is a `PageSize::Value`.
const PAGE_SIZE_VALUE_MARKER: u32 = u32::MAX;

/// A "stable" set based on a B-tree.
///
/// The implementation is based on the algorithm outlined in "Introduction to Algorithms"
/// by Cormen et al.
pub struct BTreeSet<K, M>
where
    K: Storable + Ord + Clone,
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

    // A marker to communicate to the Rust compiler that we own these types.
    _phantom: PhantomData<(K)>,
}

/// The packed header size must be <= ALLOCATOR_OFFSET.
struct BTreeHeader {
    version: Version,
    root_addr: Address,
    length: u64,
    // Reserved bytes for future extensions
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
    pub fn init(memory: M) -> Self {
        if memory.size() == 0 {
            // Memory is empty. Create a new map.
            return BTreeSet::new(memory);
        }

        // Check if the magic in the memory corresponds to a BTreeSet.
        let mut dst = vec![0; 3];
        memory.read(0, &mut dst);
        if dst != MAGIC {
            // No BTreeSet found. Create a new instance.
            BTreeSet::new(memory)
        } else {
            // The memory already contains a BTreeSet. Load it.
            BTreeSet::load(memory)
        }
    }
}
