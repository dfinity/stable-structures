//! A module for simulating multiple memories within a single memory.
//!
//! The typical way for a canister to have multiple stable structures is by dividing the memory into
//! distinct ranges, dedicating each range to a stable structure. This approach has two problems:
//!
//! 1. The developer needs to put in advance an upper bound on the memory of each stable structure.
//! 2. It wastes the canister's memory allocation. For example, if a canister creates two stable
//! structures A and B, and gives each one of them a 1GiB region of memory, then writing to B will
//! require growing > 1GiB of memory just to be able to write to it.
//!
//! The [`MemoryManager`] in this module solves both of these problems. It simulates having
//! multiple memories, each being able to grow without bound. That way, a developer doesn't need to
//! put an upper bound to how much stable structures can grow, and the canister's memory allocation
//! becomes less wasteful.
//!
//! Example Usage:
//!
//! ```
//! use ic_stable_structures::{DefaultMemoryImpl, Memory};
//! use ic_stable_structures::memory_manager::{MemoryManager, MemoryId};
//!
//! let mem_mgr = MemoryManager::init(DefaultMemoryImpl::default());
//!
//! // Create different memories, each with a unique ID.
//! let memory_0 = mem_mgr.get(MemoryId::new(0));
//! let memory_1 = mem_mgr.get(MemoryId::new(1));
//!
//! // Each memory can be used independently.
//! memory_0.grow(1);
//! memory_0.write(0, &[1, 2, 3]);
//!
//! memory_1.grow(1);
//! memory_1.write(0, &[4, 5, 6]);
//!
//! let mut bytes = vec![0; 3];
//! memory_0.read(0, &mut bytes);
//! assert_eq!(bytes, vec![1, 2, 3]);
//!
//! let mut bytes = vec![0; 3];
//! memory_1.read(0, &mut bytes);
//! assert_eq!(bytes, vec![4, 5, 6]);
//! ```

use crate::{
    read_struct,
    types::{Address, Bytes},
    write, write_struct, Memory, WASM_PAGE_SIZE,
};
use bitvec::array::BitArray;
use bitvec::macros::internal::funty::Fundamental;
use std::cmp::min;
use std::collections::BTreeMap;
use std::mem::{size_of, transmute};
use std::rc::Rc;
use std::{cell::RefCell, collections::BTreeSet};

const MAGIC: &[u8; 3] = b"MGR";
const LAYOUT_VERSION_V1: u8 = 1;
const LAYOUT_VERSION_V2: u8 = 2;

// The maximum number of memories that can be created.
const MAX_NUM_MEMORIES: u8 = 255;

// The maximum number of buckets the memory manager can handle.
// With a bucket size of 128 pages this can support up to 256GiB of memory.
const MAX_NUM_BUCKETS: u64 = 32768;

const BUCKET_SIZE_IN_PAGES: u64 = 128;

// A value used internally to indicate that a bucket is unallocated.
const UNALLOCATED_BUCKET_MARKER: u8 = MAX_NUM_MEMORIES;

// The offset where buckets are in memory.
const BUCKETS_OFFSET_IN_PAGES: u64 = 1;
const BUCKETS_OFFSET_IN_BYTES: u64 = BUCKETS_OFFSET_IN_PAGES * WASM_PAGE_SIZE;

const BUCKET_BITS_OFFSET: u64 = size_of::<Header>() as u64;

// Reserved bytes in the header for future extensions.
const HEADER_RESERVED_BYTES: usize = 32;

/// A memory manager simulates multiple memories within a single memory.
///
/// The memory manager can return up to 255 unique instances of [`VirtualMemory`], and each can be
/// used independently and can grow up to the bounds of the underlying memory.
///
/// By default, the memory manager divides the memory into "buckets" of 128 pages. Each
/// [`VirtualMemory`] is internally represented as a list of buckets. Buckets of different memories
/// can be interleaved, but the [`VirtualMemory`] interface gives the illusion of a continuous
/// address space.
///
/// Because a [`VirtualMemory`] is a list of buckets, this implies that internally it grows one
/// bucket at a time.
///
/// The first page of the memory is reserved for the memory manager's own state. The layout for
/// this state is as follows:
///
/// # V1 layout
///
/// ```text
/// -------------------------------------------------- <- Address 0
/// Magic "MGR"                           ↕ 3 bytes
/// --------------------------------------------------
/// Layout version                        ↕ 1 byte
/// --------------------------------------------------
/// Number of allocated buckets           ↕ 2 bytes
/// --------------------------------------------------
/// Bucket size (in pages) = N            ↕ 2 bytes
/// --------------------------------------------------
/// Reserved space                        ↕ 32 bytes
/// --------------------------------------------------
/// Size of memory 0 (in pages)           ↕ 8 bytes
/// --------------------------------------------------
/// Size of memory 1 (in pages)           ↕ 8 bytes
/// --------------------------------------------------
/// ...
/// --------------------------------------------------
/// Size of memory 254 (in pages)         ↕ 8 bytes
/// -------------------------------------------------- <- Bucket allocations
/// Bucket 1                              ↕ 1 byte        (1 byte indicating which memory owns it)
/// --------------------------------------------------
/// Bucket 2                              ↕ 1 byte
/// --------------------------------------------------
/// ...
/// --------------------------------------------------
/// Bucket `MAX_NUM_BUCKETS`              ↕ 1 byte
/// --------------------------------------------------
/// Unallocated space                     ↕ 30'688 bytes
/// -------------------------------------------------- <- Buckets (Page 1)
/// Bucket 1                              ↕ N pages
/// -------------------------------------------------- <- Page N + 1
/// Bucket 2                              ↕ N pages
/// --------------------------------------------------
/// ...
/// -------------------------------------------------- <- Page ((MAX_NUM_BUCKETS - 1) * N + 1)
/// Bucket MAX_NUM_BUCKETS                ↕ N pages
///
/// # V2 layout
///
/// ```text
/// -------------------------------------------------- <- Address 0
/// Magic "MGR"                             ↕ 3 bytes
/// --------------------------------------------------
/// Layout version                          ↕ 1 byte
/// --------------------------------------------------
/// Number of allocated buckets             ↕ 2 bytes
/// --------------------------------------------------
/// Bucket size (in pages) = N              ↕ 2 bytes
/// --------------------------------------------------
/// Reserved space                          ↕ 32 bytes
/// --------------------------------------------------
/// Size of memory 0 (in pages)             ↕ 8 bytes
/// --------------------------------------------------
/// Size of memory 1 (in pages)             ↕ 8 bytes
/// --------------------------------------------------
/// ...
/// --------------------------------------------------
/// Size of memory 254 (in pages)           ↕ 8 bytes
/// -------------------------------------------------- <- IDs of buckets
/// First bucket belonging to memory 0      ↕ 2 bytes
/// --------------------------------------------------
/// First bucket belonging to memory 1      ↕ 2 bytes
/// --------------------------------------------------
/// ...
/// --------------------------------------------------
/// First bucket belonging to memory 254    ↕ 2 bytes
/// --------------------------------------------------
/// Next bucket in linked list after bucket 1 ↕ 15 bits
/// --------------------------------------------------
/// Next bucket in linked list after bucket 2 ↕ 15 bits
/// --------------------------------------------------
/// ...
/// ---------------------------------------------------
/// Next bucket in linked list after bucket MAX_NUM_BUCKETS ↕ 15 bits
/// --------------------------------------------------
/// Unallocated space                       ↕ 1'506 bytes
/// -------------------------------------------------- <- Buckets (Page 1)
/// Bucket 1                                ↕ N pages
/// -------------------------------------------------- <- Page N + 1
/// Bucket 2                                ↕ N pages
/// --------------------------------------------------
/// ...
/// -------------------------------------------------- <- Page ((MAX_NUM_BUCKETS - 1) * N + 1)
/// Bucket MAX_NUM_BUCKETS                  ↕ N pages
/// ```
pub struct MemoryManager<M: Memory> {
    inner: Rc<RefCell<MemoryManagerInner<M>>>,
}

impl<M: Memory> MemoryManager<M> {
    /// Initializes a `MemoryManager` with the given memory.
    pub fn init(memory: M) -> Self {
        Self::init_with_bucket_size(memory, BUCKET_SIZE_IN_PAGES as u16)
    }

    /// Initializes a `MemoryManager` with the given memory and bucket size in pages.
    pub fn init_with_bucket_size(memory: M, bucket_size_in_pages: u16) -> Self {
        Self {
            inner: Rc::new(RefCell::new(MemoryManagerInner::init(
                memory,
                bucket_size_in_pages,
            ))),
        }
    }

    #[cfg(test)]
    pub fn init_with_bucket_size_v1(memory: M, bucket_size_in_pages: u16) -> Self {
        Self {
            inner: Rc::new(RefCell::new(MemoryManagerInner::init_v1(
                memory,
                bucket_size_in_pages,
            ))),
        }
    }

    /// Returns the memory associated with the given ID.
    pub fn get(&self, id: MemoryId) -> VirtualMemory<M> {
        VirtualMemory {
            id,
            memory_manager: self.inner.clone(),
        }
    }

    /// Returns the underlying memory.
    ///
    /// # Returns
    /// - The underlying memory, if there is exactly one strong reference to the memory manager.  Please see [`Rc::try_unwrap`](https://doc.rust-lang.org/std/rc/struct.Rc.html#method.try_unwrap) for more details.
    /// - None otherwise.
    pub fn into_memory(self) -> Option<M> {
        Rc::into_inner(self.inner).map(|inner| inner.into_inner().into_memory())
    }

    /// Frees the specified memory.
    /// Note that the underlying physical memory doesn't shrink, but the space previously
    /// occupied by the given memory will be reused.
    pub fn free(&mut self, id: MemoryId) {
        self.inner.borrow_mut().free(id);
    }
}

#[repr(C, packed)]
struct Header {
    magic: [u8; 3],

    version: u8,

    // The number of buckets allocated by the memory manager.
    num_allocated_buckets: u16,

    // The size of a bucket in Wasm pages.
    bucket_size_in_pages: u16,

    // Reserved bytes for future extensions
    _reserved: [u8; HEADER_RESERVED_BYTES],

    // The size of each individual memory that can be created by the memory manager.
    memory_sizes_in_pages: [u64; MAX_NUM_MEMORIES as usize],
}

impl Header {
    fn size() -> Bytes {
        Bytes::new(core::mem::size_of::<Self>() as u64)
    }
}

#[derive(Clone)]
pub struct VirtualMemory<M: Memory> {
    id: MemoryId,
    memory_manager: Rc<RefCell<MemoryManagerInner<M>>>,
}

impl<M: Memory> Memory for VirtualMemory<M> {
    fn size(&self) -> u64 {
        self.memory_manager.borrow().memory_size(self.id)
    }

    fn grow(&self, pages: u64) -> i64 {
        self.memory_manager.borrow_mut().grow(self.id, pages)
    }

    fn read(&self, offset: u64, dst: &mut [u8]) {
        self.memory_manager.borrow().read(self.id, offset, dst)
    }

    fn write(&self, offset: u64, src: &[u8]) {
        self.memory_manager.borrow().write(self.id, offset, src)
    }
}

#[derive(Clone)]
struct MemoryManagerInner<M: Memory> {
    memory: M,

    version: u8,

    // The number of buckets that have been allocated.
    allocated_buckets: u16,

    bucket_size_in_pages: u16,

    // An array storing the size (in pages) of each of the managed memories.
    memory_sizes_in_pages: [u64; MAX_NUM_MEMORIES as usize],

    // A map mapping each managed memory to the bucket ids that are allocated to it.
    memory_buckets: BTreeMap<MemoryId, Vec<BucketId>>,

    // Tracks the buckets that were freed to be reused in future calls to `grow`.
    // NOTE: A BTreeSet is used so that bucket IDs are maintained in sorted order.
    freed_buckets: BTreeSet<BucketId>,

    bucket_bits: BucketBits,
}

impl<M: Memory> MemoryManagerInner<M> {
    fn init(memory: M, bucket_size_in_pages: u16) -> Self {
        if memory.size() == 0 {
            // Memory is empty. Create a new map.
            return Self::new(memory, bucket_size_in_pages);
        }

        // Check if the magic in the memory corresponds to this object.
        let mut dst = vec![0; 3];
        memory.read(0, &mut dst);
        if dst != MAGIC {
            // No memory manager found. Create a new instance.
            MemoryManagerInner::new(memory, bucket_size_in_pages)
        } else {
            // The memory already contains a memory manager. Load it.
            MemoryManagerInner::load(memory)
        }
    }

    fn new(memory: M, bucket_size_in_pages: u16) -> Self {
        let mem_mgr = Self {
            memory,
            version: LAYOUT_VERSION_V2,
            allocated_buckets: 0,
            memory_sizes_in_pages: [0; MAX_NUM_MEMORIES as usize],
            memory_buckets: BTreeMap::new(),
            bucket_size_in_pages,
            freed_buckets: BTreeSet::new(),
            bucket_bits: BucketBits::default(),
        };

        mem_mgr.save_header();

        mem_mgr
    }

    #[cfg(test)]
    fn init_v1(memory: M, bucket_size_in_pages: u16) -> Self {
        if memory.size() == 0 {
            // Memory is empty. Create a new map.
            return Self::new_v1(memory, bucket_size_in_pages);
        }

        // Check if the magic in the memory corresponds to this object.
        let mut dst = vec![0; 3];
        memory.read(0, &mut dst);
        if dst != MAGIC {
            // No memory manager found. Create a new instance.
            MemoryManagerInner::new_v1(memory, bucket_size_in_pages)
        } else {
            // The memory already contains a memory manager. Load it.
            MemoryManagerInner::load(memory)
        }
    }

    #[cfg(test)]
    fn new_v1(memory: M, bucket_size_in_pages: u16) -> Self {
        let mem_mgr = Self {
            memory,
            version: LAYOUT_VERSION_V1,
            allocated_buckets: 0,
            memory_sizes_in_pages: [0; MAX_NUM_MEMORIES as usize],
            memory_buckets: BTreeMap::new(),
            bucket_size_in_pages,
            freed_buckets: BTreeSet::new(),
            bucket_bits: BucketBits::default(),
        };

        mem_mgr.save_header_v1();

        // Mark all the buckets as unallocated.
        crate::write(
            &mem_mgr.memory,
            bucket_allocations_address(BucketId(0)).get(),
            &[UNALLOCATED_BUCKET_MARKER; MAX_NUM_BUCKETS as usize],
        );

        mem_mgr
    }

    fn load_layout_v1(memory: M, header: Header) -> Self {
        let mut buckets = vec![0; MAX_NUM_BUCKETS as usize];
        memory.read(bucket_allocations_address(BucketId(0)).get(), &mut buckets);
        let mut memory_buckets = BTreeMap::new();

        for (bucket_idx, memory) in buckets.into_iter().enumerate() {
            if memory != UNALLOCATED_BUCKET_MARKER {
                memory_buckets
                    .entry(MemoryId(memory))
                    .or_insert_with(Vec::new)
                    .push(BucketId(bucket_idx as u16));
            }
        }

        let mut bucket_bits = BucketBits::default();
        for (memory_id, buckets) in memory_buckets.iter() {
            let mut previous = BucketId(0);
            for (index, bucket) in buckets.iter().enumerate() {
                if index == 0 {
                    bucket_bits.set_first(*memory_id, *bucket)
                } else {
                    bucket_bits.set_next(previous, *bucket);
                }
                previous = *bucket;
            }
        }

        bucket_bits.flush_all(&memory, BUCKET_BITS_OFFSET);

        let mem_mgr = Self {
            memory,
            version: LAYOUT_VERSION_V2,
            allocated_buckets: header.num_allocated_buckets,
            bucket_size_in_pages: header.bucket_size_in_pages,
            memory_sizes_in_pages: header.memory_sizes_in_pages,
            memory_buckets,
            freed_buckets: BTreeSet::new(),
            bucket_bits,
        };
        mem_mgr.save_header();
        mem_mgr
    }

    fn load_layout_v2(memory: M, header: Header) -> Self {
        let mut memory_size_in_buckets = vec![];

        // Map of all memories with their assigned buckets.
        let mut memory_buckets = BTreeMap::new();

        let bucket_bits: BucketBits =
            read_struct::<BucketBitsPacked, _>(Address::from(BUCKET_BITS_OFFSET), &memory).into();

        // Translate memory sizes expressed in pages to sizes expressed in buckets.
        for (index, memory_size_in_pages) in header.memory_sizes_in_pages.into_iter().enumerate() {
            let memory_id = MemoryId(index as u8);
            let size_in_buckets = memory_size_in_pages.div_ceil(header.bucket_size_in_pages as u64);
            memory_size_in_buckets.push(size_in_buckets);

            if size_in_buckets > 0 {
                let buckets = bucket_bits.buckets_for_memory(memory_id, size_in_buckets as u16);
                memory_buckets.insert(memory_id, buckets);
            }
        }

        // Set of all buckets with ID smaller than 'max_bucket_id' which were allocated and freed.
        let mut freed_buckets: BTreeSet<BucketId> =
            (0..header.num_allocated_buckets).map(BucketId).collect();

        for bucket_id in memory_buckets.values().flat_map(|buckets| buckets.iter()) {
            freed_buckets.remove(bucket_id);
        }

        Self {
            memory,
            version: LAYOUT_VERSION_V2,
            allocated_buckets: header.num_allocated_buckets,
            bucket_size_in_pages: header.bucket_size_in_pages,
            memory_sizes_in_pages: header.memory_sizes_in_pages,
            memory_buckets,
            freed_buckets,
            bucket_bits,
        }
    }

    fn load(memory: M) -> Self {
        // Read the header from memory.
        let header: Header = read_struct(Address::from(0), &memory);
        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        match header.version {
            LAYOUT_VERSION_V1 => MemoryManagerInner::load_layout_v1(memory, header),
            LAYOUT_VERSION_V2 => MemoryManagerInner::load_layout_v2(memory, header),
            _ => panic!("Unsupported version."),
        }
    }

    fn save_header(&self) {
        let header = Header {
            magic: *MAGIC,
            version: self.version,
            num_allocated_buckets: self.allocated_buckets,
            bucket_size_in_pages: self.bucket_size_in_pages,
            _reserved: [0; HEADER_RESERVED_BYTES],
            memory_sizes_in_pages: self.memory_sizes_in_pages,
        };

        write_struct(&header, Address::from(0), &self.memory);
    }

    // Returns the size of a memory (in pages).
    fn memory_size(&self, id: MemoryId) -> u64 {
        self.memory_sizes_in_pages[id.0 as usize]
    }

    // Grows the memory with the given id by the given number of pages.
    fn grow(&mut self, id: MemoryId, pages: u64) -> i64 {
        #[cfg(test)]
        if self.version == LAYOUT_VERSION_V1 {
            return self.grow_v1(id, pages);
        }

        debug_assert_eq!(self.version, LAYOUT_VERSION_V2);

        // Compute how many additional buckets are needed.
        let old_size = self.memory_size(id);
        let new_size = old_size + pages;
        let current_buckets = self.num_buckets_needed(old_size);
        let required_buckets = self.num_buckets_needed(new_size);
        let new_buckets_needed = required_buckets - current_buckets;

        if new_buckets_needed + self.allocated_buckets as u64 - self.freed_buckets.len() as u64
            > MAX_NUM_BUCKETS
        {
            // Exceeded the memory that can be managed.
            return -1;
        }

        // Allocate new buckets as needed.
        for _ in 0..new_buckets_needed {
            let new_bucket_id = match self.freed_buckets.pop_first() {
                Some(t) => t,
                None => {
                    let new_id = self.allocated_buckets;
                    self.allocated_buckets += 1;
                    BucketId(new_id)
                }
            };

            let buckets = self.memory_buckets.entry(id).or_default();
            if let Some(last_bucket) = buckets.last() {
                self.bucket_bits.set_next(*last_bucket, new_bucket_id);
            } else {
                self.bucket_bits.set_first(id, new_bucket_id);
            }
            buckets.push(new_bucket_id);
        }

        // Grow the underlying memory if necessary.
        let pages_needed = BUCKETS_OFFSET_IN_PAGES
            + self.bucket_size_in_pages as u64 * self.allocated_buckets as u64;
        if pages_needed > self.memory.size() {
            let additional_pages_needed = pages_needed - self.memory.size();
            let prev_pages = self.memory.grow(additional_pages_needed);
            if prev_pages == -1 {
                panic!("{id:?}: grow failed");
            }
        }

        // Update the memory with the new size.
        self.memory_sizes_in_pages[id.0 as usize] = new_size;

        // Update the header.
        self.save_header();

        // Write in stable store that this bucket belongs to the memory with the provided `id`.
        self.bucket_bits
            .flush_dirty_bytes(&self.memory, BUCKET_BITS_OFFSET);

        // Return the old size.
        old_size as i64
    }

    #[cfg(test)]
    fn grow_v1(&mut self, id: MemoryId, pages: u64) -> i64 {
        // Compute how many additional buckets are needed.
        let old_size = self.memory_size(id);
        let new_size = old_size + pages;
        let current_buckets = self.num_buckets_needed(old_size);
        let required_buckets = self.num_buckets_needed(new_size);
        let new_buckets_needed = required_buckets - current_buckets;

        if new_buckets_needed + self.allocated_buckets as u64 > MAX_NUM_BUCKETS {
            // Exceeded the memory that can be managed.
            return -1;
        }

        // Allocate new buckets as needed.
        for _ in 0..new_buckets_needed {
            let new_bucket_id = BucketId(self.allocated_buckets);

            self.memory_buckets
                .entry(id)
                .or_default()
                .push(new_bucket_id);

            // Write in stable store that this bucket belongs to the memory with the provided `id`.
            write(
                &self.memory,
                bucket_allocations_address(new_bucket_id).get(),
                &[id.0],
            );

            self.allocated_buckets += 1;
        }

        // Grow the underlying memory if necessary.
        let pages_needed = BUCKETS_OFFSET_IN_PAGES
            + self.bucket_size_in_pages as u64 * self.allocated_buckets as u64;
        if pages_needed > self.memory.size() {
            let additional_pages_needed = pages_needed - self.memory.size();
            let prev_pages = self.memory.grow(additional_pages_needed);
            if prev_pages == -1 {
                panic!("{id:?}: grow failed");
            }
        }

        // Update the memory with the new size.
        self.memory_sizes_in_pages[id.0 as usize] = new_size;

        // Update the header and return the old size.
        self.save_header();
        old_size as i64
    }

    fn write(&self, id: MemoryId, offset: u64, src: &[u8]) {
        if (offset + src.len() as u64) > self.memory_size(id) * WASM_PAGE_SIZE {
            panic!("{id:?}: write out of bounds");
        }

        let mut bytes_written = 0;
        for Segment { address, length } in self.bucket_iter(id, offset, src.len()) {
            self.memory.write(
                address.get(),
                &src[bytes_written as usize..(bytes_written + length.get()) as usize],
            );

            bytes_written += length.get();
        }
    }

    fn read(&self, id: MemoryId, offset: u64, dst: &mut [u8]) {
        if (offset + dst.len() as u64) > self.memory_size(id) * WASM_PAGE_SIZE {
            panic!("{id:?}: read out of bounds");
        }

        let mut bytes_read = 0;
        for Segment { address, length } in self.bucket_iter(id, offset, dst.len()) {
            self.memory.read(
                address.get(),
                &mut dst[bytes_read as usize..(bytes_read + length.get()) as usize],
            );

            bytes_read += length.get();
        }
    }

    // Initializes a [`BucketIterator`].
    fn bucket_iter(&self, id: MemoryId, offset: u64, length: usize) -> BucketIterator {
        // Get the buckets allocated to the given memory id.
        let buckets = match self.memory_buckets.get(&id) {
            Some(s) => s.as_slice(),
            None => &[],
        };

        BucketIterator {
            virtual_segment: Segment {
                address: Address::from(offset),
                length: Bytes::from(length as u64),
            },
            buckets,
            bucket_size_in_bytes: self.bucket_size_in_bytes(),
        }
    }

    fn bucket_size_in_bytes(&self) -> Bytes {
        Bytes::from(self.bucket_size_in_pages as u64 * WASM_PAGE_SIZE)
    }

    // Returns the number of buckets needed to accommodate the given number of pages.
    fn num_buckets_needed(&self, num_pages: u64) -> u64 {
        // Ceiling division.
        (num_pages + self.bucket_size_in_pages as u64 - 1) / self.bucket_size_in_pages as u64
    }

    // Returns the underlying memory.
    pub fn into_memory(self) -> M {
        self.memory
    }

    fn free(&mut self, id: MemoryId) {
        self.memory_sizes_in_pages[id.0 as usize] = 0;
        let buckets = self.memory_buckets.remove(&id);
        if let Some(vec_buckets) = buckets {
            for bucket in vec_buckets {
                self.freed_buckets.insert(bucket);
            }
        }
        // Update the header.
        self.save_header();
    }

    #[cfg(test)]
    fn save_header_v1(&self) {
        let header = Header {
            magic: *MAGIC,
            version: LAYOUT_VERSION_V1,
            num_allocated_buckets: self.allocated_buckets,
            bucket_size_in_pages: self.bucket_size_in_pages,
            _reserved: [0; HEADER_RESERVED_BYTES],
            memory_sizes_in_pages: self.memory_sizes_in_pages,
        };

        write_struct(&header, Address::from(0), &self.memory);
    }
}

struct Segment {
    address: Address,
    length: Bytes,
}

// An iterator that maps a segment of virtual memory to segments of real memory.
//
// A segment in virtual memory can map to multiple segments of real memory. Here's an example:
//
// Virtual Memory
// --------------------------------------------------------
//          (A) ---------- SEGMENT ---------- (B)
// --------------------------------------------------------
// ↑               ↑               ↑               ↑
// Bucket 0        Bucket 1        Bucket 2        Bucket 3
//
// The [`VirtualMemory`] is internally divided into fixed-size buckets. In the memory's virtual
// address space, all these buckets are consecutive, but in real memory this may not be the case.
//
// A virtual segment would first be split at the bucket boundaries. The example virtual segment
// above would be split into the following segments:
//
//    (A, end of bucket 0)
//    (start of bucket 1, end of bucket 1)
//    (start of bucket 2, B)
//
// Each of the segments above can then be translated into the real address space by looking up
// the underlying buckets' addresses in real memory.
struct BucketIterator<'a> {
    virtual_segment: Segment,
    buckets: &'a [BucketId],
    bucket_size_in_bytes: Bytes,
}

impl Iterator for BucketIterator<'_> {
    type Item = Segment;

    fn next(&mut self) -> Option<Self::Item> {
        if self.virtual_segment.length == Bytes::from(0u64) {
            return None;
        }

        // Map the virtual segment's address to a real address.
        let bucket_idx =
            (self.virtual_segment.address.get() / self.bucket_size_in_bytes.get()) as usize;
        let bucket_address = self.bucket_address(
            *self
                .buckets
                .get(bucket_idx)
                .expect("bucket idx out of bounds"),
        );

        let real_address = bucket_address
            + Bytes::from(self.virtual_segment.address.get() % self.bucket_size_in_bytes.get());

        // Compute how many bytes are in this real segment.
        let bytes_in_segment = {
            let next_bucket_address = bucket_address + self.bucket_size_in_bytes;

            // Write up to either the end of the bucket, or the end of the segment.
            min(
                Bytes::from(next_bucket_address.get() - real_address.get()),
                self.virtual_segment.length,
            )
        };

        // Update the virtual segment to exclude the portion we're about to return.
        self.virtual_segment.length -= bytes_in_segment;
        self.virtual_segment.address += bytes_in_segment;

        Some(Segment {
            address: real_address,
            length: bytes_in_segment,
        })
    }
}

impl<'a> BucketIterator<'a> {
    // Returns the address of a given bucket.
    fn bucket_address(&self, id: BucketId) -> Address {
        Address::from(BUCKETS_OFFSET_IN_BYTES) + self.bucket_size_in_bytes * Bytes::from(id.0)
    }
}

#[derive(Clone, Copy, Ord, Eq, PartialEq, PartialOrd, Debug)]
pub struct MemoryId(u8);

impl MemoryId {
    pub const fn new(id: u8) -> Self {
        // Any ID can be used except the special value that's used internally to
        // mark a bucket as unallocated.
        assert!(id != UNALLOCATED_BUCKET_MARKER);

        Self(id)
    }
}

// Referring to a bucket.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct BucketId(u16);

fn bucket_allocations_address(id: BucketId) -> Address {
    Address::from(0) + Header::size() + Bytes::from(id.0)
}

const BUCKET_BITS_LEN: usize = 15 * MAX_NUM_BUCKETS as usize;

#[derive(Clone, Default)]
struct BucketBits {
    inner: BucketBitsPacked,
    dirty_first_buckets: BTreeSet<MemoryId>,
    dirty_bucket_link_bytes: BTreeSet<u16>,
}

#[derive(Clone)]
#[repr(C, packed)]
struct BucketBitsPacked {
    first_bucket_per_memory: [u16; MAX_NUM_MEMORIES as usize],
    bucket_links: BitArray<[u8; BUCKET_BITS_LEN / 8]>,
}

impl BucketBits {
    // Gets the first bucket assigned to a memory.
    // Only call this if you know that there are buckets assigned to the memory.
    fn get_first(&self, memory_id: MemoryId) -> BucketId {
        BucketId(self.inner.first_bucket_per_memory[memory_id.0 as usize])
    }

    // Sets the first bucket assigned to a memory
    fn set_first(&mut self, memory_id: MemoryId, value: BucketId) {
        self.inner.first_bucket_per_memory[memory_id.0 as usize] = value.0;
        self.dirty_first_buckets.insert(memory_id);
    }

    // Gets the next bucket in the linked list of buckets
    fn get_next(&self, bucket: BucketId) -> BucketId {
        let start_bit_index = bucket.0 as usize * 15;
        let mut next_bits: BitArray<[u8; 2]> = BitArray::new([0u8; 2]);

        for i in 0..15 {
            next_bits.set(
                i + 1,
                self.inner
                    .bucket_links
                    .get(start_bit_index + i)
                    .unwrap()
                    .as_bool(),
            );
        }

        BucketId(u16::from_be_bytes(next_bits.data))
    }

    // Sets the next bucket in the linked list of buckets
    fn set_next(&mut self, bucket: BucketId, next: BucketId) {
        let start_bit_index = bucket.0 as usize * 15;
        let next_bits: BitArray<[u8; 2]> = BitArray::from(next.0.to_be_bytes());

        for (index, bit) in next_bits.iter().skip(1).enumerate() {
            self.inner
                .bucket_links
                .set(start_bit_index + index, bit.as_bool());
        }

        let start_byte_index = start_bit_index / 8;
        let end_byte_index = (start_bit_index + 14) / 8;

        self.dirty_bucket_link_bytes
            .extend((start_byte_index..=end_byte_index).map(|i| i as u16))
    }

    // Calculates the buckets for a given memory by iterating over its linked list
    fn buckets_for_memory(&self, memory_id: MemoryId, count: u16) -> Vec<BucketId> {
        if count == 0 {
            return Vec::new();
        }

        let mut bucket = self.get_first(memory_id);
        let mut buckets = vec![bucket];
        for _ in 1..count {
            bucket = self.get_next(bucket);
            buckets.push(bucket);
        }
        buckets
    }

    // Flushes only the dirty bytes to memory
    fn flush_dirty_bytes<M: Memory>(&mut self, memory: &M, start_offset: u64) {
        const FIRST_BUCKET_PER_MEMORY_LEN: usize = 2 * MAX_NUM_MEMORIES as usize;

        if !self.dirty_first_buckets.is_empty() {
            // SAFETY: This is safe because we simply cast from [u16] to [u8] and double the length.
            let bytes: [u8; FIRST_BUCKET_PER_MEMORY_LEN] =
                unsafe { transmute(self.inner.first_bucket_per_memory) };

            // Multiply by 2 since we've converted from [u16] to [u8].
            let min = 2 * self.dirty_first_buckets.first().unwrap().0 as usize;
            let max = 2 * self.dirty_first_buckets.last().unwrap().0 as usize + 1;

            let slice = &bytes[min..=max];
            write(memory, start_offset + min as u64, slice);
            self.dirty_first_buckets.clear();
        }

        if !self.dirty_bucket_link_bytes.is_empty() {
            let min = *self.dirty_bucket_link_bytes.first().unwrap() as usize;
            let max = *self.dirty_bucket_link_bytes.last().unwrap() as usize;

            let slice = &self.inner.bucket_links.data[min..=max];
            write(
                memory,
                start_offset + (FIRST_BUCKET_PER_MEMORY_LEN + min) as u64,
                slice,
            );
            self.dirty_bucket_link_bytes.clear();
        }
    }

    // Flushes all bytes to memory
    fn flush_all<M: Memory>(&mut self, memory: &M, start_offset: u64) {
        write_struct(&self.inner, Address::from(start_offset), memory);
        self.dirty_first_buckets.clear();
        self.dirty_bucket_link_bytes.clear();
    }
}

impl Default for BucketBitsPacked {
    fn default() -> Self {
        BucketBitsPacked {
            first_bucket_per_memory: [0; MAX_NUM_MEMORIES as usize],
            bucket_links: BitArray::new([0u8; BUCKET_BITS_LEN / 8]),
        }
    }
}

impl From<BucketBitsPacked> for BucketBits {
    fn from(value: BucketBitsPacked) -> Self {
        BucketBits {
            inner: value,
            dirty_first_buckets: BTreeSet::new(),
            dirty_bucket_link_bytes: BTreeSet::new(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use maplit::btreemap;
    use proptest::prelude::*;

    const MAX_MEMORY_IN_PAGES: u64 = MAX_NUM_BUCKETS * BUCKET_SIZE_IN_PAGES;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn can_get_memory() {
        let mem_mgr = MemoryManager::init(make_memory());
        let memory = mem_mgr.get(MemoryId(0));
        assert_eq!(memory.size(), 0);
    }

    #[test]
    fn can_allocate_and_use_memory() {
        let mem_mgr = MemoryManager::init(make_memory());
        let memory = mem_mgr.get(MemoryId(0));
        assert_eq!(memory.grow(1), 0);
        assert_eq!(memory.size(), 1);

        memory.write(0, &[1, 2, 3]);

        let mut bytes = vec![0; 3];
        memory.read(0, &mut bytes);
        assert_eq!(bytes, vec![1, 2, 3]);

        assert_eq!(
            mem_mgr.inner.borrow().memory_buckets,
            btreemap! {
                MemoryId(0) => vec![BucketId(0)]
            }
        );
    }

    #[test]
    fn can_allocate_and_use_multiple_memories() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem.clone());
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(memory_1.grow(1), 0);

        assert_eq!(memory_0.size(), 1);
        assert_eq!(memory_1.size(), 1);

        assert_eq!(
            mem_mgr.inner.borrow().memory_buckets,
            btreemap! {
                MemoryId(0) => vec![BucketId(0)],
                MemoryId(1) => vec![BucketId(1)],
            }
        );

        memory_0.write(0, &[1, 2, 3]);
        memory_0.write(0, &[1, 2, 3]);
        memory_1.write(0, &[4, 5, 6]);

        let mut bytes = vec![0; 3];
        memory_0.read(0, &mut bytes);
        assert_eq!(bytes, vec![1, 2, 3]);

        let mut bytes = vec![0; 3];
        memory_1.read(0, &mut bytes);
        assert_eq!(bytes, vec![4, 5, 6]);

        // + 1 is for the header.
        assert_eq!(mem.size(), 2 * BUCKET_SIZE_IN_PAGES + 1);
    }

    #[test]
    fn can_be_reinitialized_from_memory() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem.clone());
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(memory_1.grow(1), 0);

        memory_0.write(0, &[1, 2, 3]);
        memory_1.write(0, &[4, 5, 6]);

        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        let mut bytes = vec![0; 3];
        memory_0.read(0, &mut bytes);
        assert_eq!(bytes, vec![1, 2, 3]);

        memory_1.read(0, &mut bytes);
        assert_eq!(bytes, vec![4, 5, 6]);
    }

    #[test]
    fn growing_same_memory_multiple_times_doesnt_increase_underlying_allocation() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem.clone());
        let memory_0 = mem_mgr.get(MemoryId(0));

        // Grow the memory by 1 page. This should increase the underlying allocation
        // by `BUCKET_SIZE_IN_PAGES` pages.
        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES);

        // Grow the memory again. This should NOT increase the underlying allocation.
        assert_eq!(memory_0.grow(1), 1);
        assert_eq!(memory_0.size(), 2);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES);

        // Grow the memory up to the BUCKET_SIZE_IN_PAGES. This should NOT increase the underlying
        // allocation.
        assert_eq!(memory_0.grow(BUCKET_SIZE_IN_PAGES - 2), 2);
        assert_eq!(memory_0.size(), BUCKET_SIZE_IN_PAGES);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES);

        // Grow the memory by one more page. This should increase the underlying allocation.
        assert_eq!(memory_0.grow(1), BUCKET_SIZE_IN_PAGES as i64);
        assert_eq!(memory_0.size(), BUCKET_SIZE_IN_PAGES + 1);
        assert_eq!(mem.size(), 1 + 2 * BUCKET_SIZE_IN_PAGES);
    }

    #[test]
    fn does_not_grow_memory_unnecessarily() {
        let mem = make_memory();
        let initial_size = BUCKET_SIZE_IN_PAGES * 2;

        // Grow the memory manually before passing it into the memory manager.
        mem.grow(initial_size);

        let mem_mgr = MemoryManager::init(mem.clone());
        let memory_0 = mem_mgr.get(MemoryId(0));

        // Grow the memory by 1 page.
        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(mem.size(), initial_size);

        // Grow the memory by BUCKET_SIZE_IN_PAGES more pages, which will cause the underlying
        // allocation to increase.
        assert_eq!(memory_0.grow(BUCKET_SIZE_IN_PAGES), 1);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES * 2);
    }

    #[test]
    fn growing_beyond_capacity_fails() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));

        assert_eq!(memory_0.grow(MAX_MEMORY_IN_PAGES + 1), -1);

        // Try to grow the memory by MAX_MEMORY_IN_PAGES + 1.
        assert_eq!(memory_0.grow(1), 0); // should succeed
        assert_eq!(memory_0.grow(MAX_MEMORY_IN_PAGES), -1); // should fail.
    }

    #[test]
    fn can_write_across_bucket_boundaries() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));

        assert_eq!(memory_0.grow(BUCKET_SIZE_IN_PAGES + 1), 0);

        memory_0.write(
            mem_mgr.inner.borrow().bucket_size_in_bytes().get() - 1,
            &[1, 2, 3],
        );

        let mut bytes = vec![0; 3];
        memory_0.read(
            mem_mgr.inner.borrow().bucket_size_in_bytes().get() - 1,
            &mut bytes,
        );
        assert_eq!(bytes, vec![1, 2, 3]);
    }

    #[test]
    fn can_write_across_bucket_boundaries_with_interleaving_memories() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        assert_eq!(memory_0.grow(BUCKET_SIZE_IN_PAGES), 0);
        assert_eq!(memory_1.grow(1), 0);
        assert_eq!(memory_0.grow(1), BUCKET_SIZE_IN_PAGES as i64);

        memory_0.write(
            mem_mgr.inner.borrow().bucket_size_in_bytes().get() - 1,
            &[1, 2, 3],
        );
        memory_1.write(0, &[4, 5, 6]);

        let mut bytes = vec![0; 3];
        memory_0.read(WASM_PAGE_SIZE * BUCKET_SIZE_IN_PAGES - 1, &mut bytes);
        assert_eq!(bytes, vec![1, 2, 3]);

        let mut bytes = vec![0; 3];
        memory_1.read(0, &mut bytes);
        assert_eq!(bytes, vec![4, 5, 6]);
    }

    #[test]
    #[should_panic]
    fn reading_out_of_bounds_should_panic() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(memory_1.grow(1), 0);

        let mut bytes = vec![0; WASM_PAGE_SIZE as usize + 1];
        memory_0.read(0, &mut bytes);
    }

    #[test]
    #[should_panic]
    fn writing_out_of_bounds_should_panic() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(memory_1.grow(1), 0);

        let bytes = vec![0; WASM_PAGE_SIZE as usize + 1];
        memory_0.write(0, &bytes);
    }

    #[test]
    fn reading_zero_bytes_from_empty_memory_should_not_panic() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));

        assert_eq!(memory_0.size(), 0);
        let mut bytes = vec![];
        memory_0.read(0, &mut bytes);
    }

    #[test]
    fn writing_zero_bytes_to_empty_memory_should_not_panic() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));

        assert_eq!(memory_0.size(), 0);
        memory_0.write(0, &[]);
    }

    #[test]
    fn write_and_read_random_bytes() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init_with_bucket_size(mem, 1); // very small bucket size.

        let memories: Vec<_> = (0..MAX_NUM_MEMORIES)
            .map(|id| mem_mgr.get(MemoryId(id)))
            .collect();

        proptest!(|(
            num_memories in 0..255usize,
            data in proptest::collection::vec(0..u8::MAX, 0..2*WASM_PAGE_SIZE as usize),
            offset in 0..10*WASM_PAGE_SIZE
        )| {
            for memory in memories.iter().take(num_memories) {
                // Write a random blob into the memory, growing the memory as it needs to.
                crate::write(memory, offset, &data);

                // Verify the blob can be read back.
                let mut bytes = vec![0; data.len()];
                memory.read(offset, &mut bytes);
                assert_eq!(bytes, data);
            }
        });
    }

    #[test]
    fn init_with_non_default_bucket_size() {
        // Choose a bucket size that's different from the default bucket size.
        let bucket_size = 256;
        assert_ne!(bucket_size, BUCKET_SIZE_IN_PAGES as u16);

        // Initialize the memory manager.
        let mem = make_memory();
        let mem_mgr = MemoryManager::init_with_bucket_size(mem.clone(), bucket_size);

        // Do some writes.
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));
        memory_0.grow(300);
        memory_1.grow(100);
        memory_0.write(0, &[1; 1000]);
        memory_1.write(0, &[2; 1000]);

        // Reinitializes the memory manager using the `init` method, without specifying
        // the bucket size.
        let mem_mgr = MemoryManager::init(mem);

        // Assert the bucket size is correct.
        assert_eq!(mem_mgr.inner.borrow().bucket_size_in_pages, bucket_size);

        // Assert that the data written is correct.
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        assert_eq!(memory_0.size(), 300);
        assert_eq!(memory_1.size(), 100);

        let mut buf = vec![0; 1000];
        memory_0.read(0, &mut buf);
        assert_eq!(buf, vec![1; 1000]);

        memory_1.read(0, &mut buf);
        assert_eq!(buf, vec![2; 1000]);
    }

    #[test]
    fn free_memory_works() {
        let mem = make_memory();
        let mut mem_mgr = MemoryManager::init(mem.clone());
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));

        // Grow the memory by 1 page.
        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(mem.size(), BUCKET_SIZE_IN_PAGES + 1);

        // Grow the memory by 1 page.
        assert_eq!(memory_1.grow(1), 0);
        assert_eq!(mem.size(), 2 * BUCKET_SIZE_IN_PAGES + 1);

        // Grow the memory by BUCKET_SIZE_IN_PAGES more pages, which will cause the underlying
        // allocation to increase.
        assert_eq!(memory_0.grow(BUCKET_SIZE_IN_PAGES), 1);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES * 3);
        assert_eq!(memory_1.grow(BUCKET_SIZE_IN_PAGES), 1);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES * 4);
        assert_eq!(mem_mgr.get(MemoryId(1)).size(), 1 + BUCKET_SIZE_IN_PAGES);

        // Free Memory ID 1.
        mem_mgr.free(MemoryId(1));
        assert_eq!(mem_mgr.get(MemoryId(1)).size(), 0);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES * 4);

        let memory_2 = mem_mgr.get(MemoryId(2));
        // When growing memory_2, mem.size() should stay the same since
        // MemoryManager should use the memory that is freed above.
        assert_eq!(memory_2.grow(1), 0);
        assert_eq!(mem_mgr.get(MemoryId(2)).size(), 1);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES * 4);
        assert_eq!(memory_2.grow(BUCKET_SIZE_IN_PAGES), 1);
        assert_eq!(mem_mgr.get(MemoryId(2)).size(), 1 + BUCKET_SIZE_IN_PAGES);
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES * 4);

        // When trying to grow memory_2 again, we need more pages,
        // because we have already used all that is left from Memory ID 1.
        assert_ne!(memory_2.grow(BUCKET_SIZE_IN_PAGES), 0);
        assert_eq!(
            mem_mgr.get(MemoryId(2)).size(),
            1 + 2 * BUCKET_SIZE_IN_PAGES
        );
        assert_eq!(mem.size(), 1 + BUCKET_SIZE_IN_PAGES * 5);
    }

    #[test]
    #[should_panic = "MemoryId(1): read out of bounds"]
    fn reading_freed_memory_panics() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init(mem.clone());
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));
        let memory_2 = mem_mgr.get(MemoryId(2));

        assert_eq!(memory_0.grow(1), 0);
        assert_eq!(memory_1.grow(1), 0);
        assert_eq!(memory_2.grow(1), 0);

        memory_0.write(0, &[1, 2, 3]);
        memory_1.write(0, &[4, 5, 6]);
        memory_2.write(0, &[7, 8, 9]);

        let mut mem_mgr = MemoryManager::init(mem);
        let memory_0 = mem_mgr.get(MemoryId(0));
        let memory_1 = mem_mgr.get(MemoryId(1));
        let memory_2 = mem_mgr.get(MemoryId(2));

        let mut bytes = vec![0; 3];
        // Check that data is correctly reinitialized.
        memory_0.read(0, &mut bytes);
        assert_eq!(bytes, vec![1, 2, 3]);

        memory_1.read(0, &mut bytes);
        assert_eq!(bytes, vec![4, 5, 6]);

        memory_2.read(0, &mut bytes);
        assert_eq!(bytes, vec![7, 8, 9]);

        // Free MemoryId 1.
        mem_mgr.free(MemoryId(1));

        // Check that data of MemoryId 0 and 2 is correctly reinitialized.
        memory_0.read(0, &mut bytes);
        assert_eq!(bytes, vec![1, 2, 3]);

        memory_2.read(0, &mut bytes);
        assert_eq!(bytes, vec![7, 8, 9]);

        // Check that date of MemoryId 1 is freed.
        assert_eq!(memory_1.size(), 0);
        memory_1.read(0, &mut bytes);
    }

    #[test]
    fn freeing_already_free_memory() {
        let mut mem_mgr = MemoryManager::init(make_memory());
        let memory_0 = mem_mgr.get(MemoryId(0));

        assert_eq!(memory_0.grow(1), 0);

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 1);

        mem_mgr.free(MemoryId(0));

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 0);

        mem_mgr.free(MemoryId(0));

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 0);
    }

    #[test]
    fn grow_memory_after_freeing_it() {
        let mut mem_mgr = MemoryManager::init(make_memory());
        let memory_0 = mem_mgr.get(MemoryId(0));

        // grow and write to memory
        assert_eq!(memory_0.grow(1), 0);
        memory_0.write(0, &[7, 1, 5]);

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 1);

        let mut bytes = vec![0; 3];

        // read from memory
        memory_0.read(0, &mut bytes);
        assert_eq!(bytes, &[7, 1, 5]);

        // free memory
        mem_mgr.free(MemoryId(0));

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 0);

        // grow memory
        assert_eq!(memory_0.grow(1), 0);

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 1);

        // check that old bucket is reassign to the memory
        memory_0.read(0, &mut bytes);
        assert_eq!(bytes, &[7, 1, 5]);

        // try growing once more
        assert_eq!(memory_0.grow(1), 1);
        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 2);
    }

    #[test]
    fn test_freed_buckets_assignment_order() {
        let mut mem_mgr = MemoryManager::init(make_memory());
        let memory_a: VirtualMemory<Rc<RefCell<Vec<u8>>>> = mem_mgr.get(MemoryId(0));
        let memory_b: VirtualMemory<Rc<RefCell<Vec<u8>>>> = mem_mgr.get(MemoryId(1));

        // grow and write to memory
        assert_eq!(memory_a.grow(1), 0);
        assert_eq!(memory_b.grow(1), 0);
        memory_a.write(0, &[7, 1, 5]);
        memory_b.write(0, &[9, 4, 8]);

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 1);
        assert_eq!(mem_mgr.get(MemoryId(1)).size(), 1);

        let mut bytes = vec![0; 3];

        // free memory
        mem_mgr.free(MemoryId(0));
        mem_mgr.free(MemoryId(1));

        assert_eq!(mem_mgr.get(MemoryId(0)).size(), 0);
        assert_eq!(mem_mgr.get(MemoryId(1)).size(), 0);

        let memory_c: VirtualMemory<Rc<RefCell<Vec<u8>>>> = mem_mgr.get(MemoryId(2));
        let memory_d: VirtualMemory<Rc<RefCell<Vec<u8>>>> = mem_mgr.get(MemoryId(3));

        // grow memory
        assert_eq!(memory_c.grow(1), 0);
        assert_eq!(memory_d.grow(1), 0);

        assert_eq!(mem_mgr.get(MemoryId(2)).size(), 1);
        assert_eq!(mem_mgr.get(MemoryId(3)).size(), 1);

        // check that old bucket is reassign to the memory
        memory_c.read(0, &mut bytes);
        assert_eq!(bytes, &[7, 1, 5]);

        // check that old bucket is reassign to the memory
        memory_d.read(0, &mut bytes);
        assert_eq!(bytes, &[9, 4, 8]);
    }

    #[test]
    fn free_memory_that_was_not_used() {
        let mut mem_mgr = MemoryManager::init(make_memory());
        let memory_0 = mem_mgr.get(MemoryId(0));
        assert_eq!(memory_0.grow(1), 0);

        mem_mgr.free(MemoryId(5));
    }

    #[test]
    fn freed_memories_are_tracked() {
        let mem = make_memory();
        let mut mem_mgr = MemoryManager::init_with_bucket_size(mem.clone(), 1);
        mem_mgr.get(MemoryId(0)).grow(1);
        mem_mgr.get(MemoryId(1)).grow(2);
        mem_mgr.get(MemoryId(2)).grow(3);
        mem_mgr.get(MemoryId(3)).grow(2);
        mem_mgr.get(MemoryId(4)).grow(1);

        mem_mgr.free(MemoryId(0));
        mem_mgr.free(MemoryId(2));
        mem_mgr.free(MemoryId(4));

        let mem_mgr = MemoryManager::init(mem);
        assert_eq!(
            mem_mgr.inner.borrow().freed_buckets,
            maplit::btreeset! { BucketId(0), BucketId(3), BucketId(4), BucketId(5), BucketId(8) }
        );
    }

    #[test]
    fn upgrade_from_v1_to_v2() {
        let mem = make_memory();
        // Initialize with layout v1.
        let mem_mgr = MemoryManager::init_with_bucket_size_v1(mem.clone(), 1); // very small bucket size.

        let memories_v1: Vec<_> = (0..MAX_NUM_MEMORIES)
            .map(|id| mem_mgr.get(MemoryId(id)))
            .collect();

        proptest!(|(
            num_memories in 0..10usize,
            data in proptest::collection::vec(0..u8::MAX, 0..2*WASM_PAGE_SIZE as usize),
            offset in 0..10*WASM_PAGE_SIZE
        )| {
            for memory_v1 in memories_v1.iter().take(num_memories) {
                // Write a random blob into the memory, growing the memory as it needs to.
                crate::write(memory_v1, offset, &data);
            }

            // Copy the underlying memory because loading a v1 memory manager will convert it to v2
            let mem_clone = Rc::new(RefCell::new(mem.borrow().clone()));

            // Load layout v1 and convert it to layout v2.
            let mem_mgr_v2 = MemoryManager::init_with_bucket_size(mem_clone, 1);
            let memories_v2: Vec<_> = (0..MAX_NUM_MEMORIES)
                .map(|id| mem_mgr_v2.get(MemoryId(id)))
                .collect();

            for memory_v2 in memories_v2.iter().take(num_memories) {
                // Verify the blob can be read back.
                let mut bytes = vec![0; data.len()];
                memory_v2.read(offset, &mut bytes);
                assert_eq!(bytes, data);
            }
        });
    }
}
