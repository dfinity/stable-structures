//! A module for simulating multiple memories within a single memory.
//!
//! The typical way for a canister to have multiple stable structures is by dividing the memory into
//! distinct ranges, dedicating each range to a stable structure. This approach has two problems:
//!
//! 1. The developer needs to put in advance an upper bound on the memory of each stable structure.
//! 2. It wastes the canister's memory allocation. For example, if a canister creates two stable
//!    structures A and B, and gives each one of them a 1GiB region of memory, then writing to B will
//!    require growing > 1GiB of memory just to be able to write to it.
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
    read_struct, read_to_vec,
    types::{Address, Bytes},
    write, write_struct, Memory, WASM_PAGE_SIZE,
};
use std::cell::{Cell, RefCell};
use std::rc::Rc;

const MAGIC: &[u8; 3] = b"MGR";
const LAYOUT_VERSION: u8 = 1;

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

    /// Returns the memory associated with the given ID.
    pub fn get(&self, id: MemoryId) -> VirtualMemory<M> {
        VirtualMemory {
            id,
            memory_manager: self.inner.clone(),
            cache: BucketCache::new(),
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
}

#[repr(C, packed)]
struct Header {
    magic: [u8; 3],

    version: u8,

    /// The number of buckets allocated by the memory manager.
    num_allocated_buckets: u16,

    /// The size of a bucket in Wasm pages.
    bucket_size_in_pages: u16,

    /// Reserved bytes for future extensions
    _reserved: [u8; HEADER_RESERVED_BYTES],

    /// The size of each individual memory that can be created by the memory manager.
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
    cache: BucketCache,
}

impl<M: Memory> Memory for VirtualMemory<M> {
    fn size(&self) -> u64 {
        self.memory_manager.borrow().memory_size(self.id)
    }

    fn grow(&self, pages: u64) -> i64 {
        self.memory_manager.borrow_mut().grow(self.id, pages)
    }

    fn read(&self, offset: u64, dst: &mut [u8]) {
        self.memory_manager
            .borrow()
            .read(self.id, offset, dst, &self.cache)
    }

    unsafe fn read_unsafe(&self, offset: u64, dst: *mut u8, count: usize) {
        self.memory_manager
            .borrow()
            .read_unsafe(self.id, offset, dst, count, &self.cache)
    }

    fn write(&self, offset: u64, src: &[u8]) {
        self.memory_manager
            .borrow()
            .write(self.id, offset, src, &self.cache)
    }
}

#[derive(Clone)]
struct MemoryManagerInner<M: Memory> {
    memory: M,

    /// The number of buckets that have been allocated.
    allocated_buckets: u16,

    bucket_size_in_pages: u16,

    /// An array storing the size (in pages) of each of the managed memories.
    memory_sizes_in_pages: [u64; MAX_NUM_MEMORIES as usize],

    /// A map mapping each managed memory to the bucket ids that are allocated to it.
    memory_buckets: Vec<Vec<BucketId>>,
}

impl<M: Memory> MemoryManagerInner<M> {
    fn init(memory: M, bucket_size_in_pages: u16) -> Self {
        if memory.size() == 0 {
            // Memory is empty. Create a new map.
            return Self::new(memory, bucket_size_in_pages);
        }

        // Check if the magic in the memory corresponds to this object.
        let mut dst = [0; 3];
        memory.read(0, &mut dst);
        if &dst != MAGIC {
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
            allocated_buckets: 0,
            memory_sizes_in_pages: [0; MAX_NUM_MEMORIES as usize],
            memory_buckets: vec![vec![]; MAX_NUM_MEMORIES as usize],
            bucket_size_in_pages,
        };

        mem_mgr.save_header();

        // Mark all the buckets as unallocated.
        write(
            &mem_mgr.memory,
            bucket_allocations_address(BucketId(0)).get(),
            &[UNALLOCATED_BUCKET_MARKER; MAX_NUM_BUCKETS as usize],
        );

        mem_mgr
    }

    fn load(memory: M) -> Self {
        // Read the header from memory.
        let header: Header = read_struct(Address::from(0), &memory);
        assert_eq!(&header.magic, MAGIC, "Bad magic.");
        assert_eq!(header.version, LAYOUT_VERSION, "Unsupported version.");

        let mut buckets = vec![];
        read_to_vec(
            &memory,
            bucket_allocations_address(BucketId(0)),
            &mut buckets,
            MAX_NUM_BUCKETS as usize,
        );

        let mut memory_buckets = vec![vec![]; MAX_NUM_MEMORIES as usize];
        for (bucket_idx, memory) in buckets.into_iter().enumerate() {
            if memory != UNALLOCATED_BUCKET_MARKER {
                memory_buckets[memory as usize].push(BucketId(bucket_idx as u16));
            }
        }

        Self {
            memory,
            allocated_buckets: header.num_allocated_buckets,
            bucket_size_in_pages: header.bucket_size_in_pages,
            memory_sizes_in_pages: header.memory_sizes_in_pages,
            memory_buckets,
        }
    }

    fn save_header(&self) {
        let header = Header {
            magic: *MAGIC,
            version: LAYOUT_VERSION,
            num_allocated_buckets: self.allocated_buckets,
            bucket_size_in_pages: self.bucket_size_in_pages,
            _reserved: [0; HEADER_RESERVED_BYTES],
            memory_sizes_in_pages: self.memory_sizes_in_pages,
        };

        write_struct(&header, Address::from(0), &self.memory);
    }

    /// Returns the size of a memory (in pages).
    fn memory_size(&self, id: MemoryId) -> u64 {
        self.memory_sizes_in_pages[id.0 as usize]
    }

    /// Grows the memory with the given id by the given number of pages.
    fn grow(&mut self, id: MemoryId, pages: u64) -> i64 {
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

        let memory_bucket = &mut self.memory_buckets[id.0 as usize];
        // Allocate new buckets as needed.
        memory_bucket.reserve(new_buckets_needed as usize);
        for _ in 0..new_buckets_needed {
            let new_bucket_id = BucketId(self.allocated_buckets);
            memory_bucket.push(new_bucket_id);

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

    fn write(&self, id: MemoryId, offset: u64, src: &[u8], bucket_cache: &BucketCache) {
        if let Some(real_address) = bucket_cache.get(VirtualSegment {
            address: offset.into(),
            length: src.len().into(),
        }) {
            self.memory.write(real_address.get(), src);
            return;
        }

        if (offset + src.len() as u64) > self.memory_size(id) * WASM_PAGE_SIZE {
            panic!("{id:?}: write out of bounds");
        }

        let mut bytes_written = 0;
        self.for_each_bucket(
            id,
            VirtualSegment {
                address: offset.into(),
                length: src.len().into(),
            },
            bucket_cache,
            |RealSegment { address, length }| {
                self.memory.write(
                    address.get(),
                    &src[bytes_written as usize..(bytes_written + length.get()) as usize],
                );

                bytes_written += length.get();
            },
        );
    }

    #[inline]
    fn read(&self, id: MemoryId, offset: u64, dst: &mut [u8], bucket_cache: &BucketCache) {
        // SAFETY: this is trivially safe because dst has dst.len() space.
        unsafe { self.read_unsafe(id, offset, dst.as_mut_ptr(), dst.len(), bucket_cache) }
    }

    /// # Safety
    ///
    /// Callers must guarantee that
    ///   * it is valid to write `count` number of bytes starting from `dst`,
    ///   * `dst..dst + count` does not overlap with `self`.
    unsafe fn read_unsafe(
        &self,
        id: MemoryId,
        offset: u64,
        dst: *mut u8,
        count: usize,
        bucket_cache: &BucketCache,
    ) {
        // First try to find the virtual segment in the cache.
        if let Some(real_address) = bucket_cache.get(VirtualSegment {
            address: offset.into(),
            length: count.into(),
        }) {
            self.memory.read_unsafe(real_address.get(), dst, count);
            return;
        }

        if (offset + count as u64) > self.memory_size(id) * WASM_PAGE_SIZE {
            panic!("{id:?}: read out of bounds");
        }

        let mut bytes_read = Bytes::new(0);
        self.for_each_bucket(
            id,
            VirtualSegment {
                address: offset.into(),
                length: count.into(),
            },
            bucket_cache,
            |RealSegment { address, length }| {
                self.memory.read_unsafe(
                    address.get(),
                    // The cast to usize is safe because `bytes_read` and `length` are bounded by
                    // usize `count`.
                    dst.add(bytes_read.get() as usize),
                    length.get() as usize,
                );

                bytes_read += length;
            },
        )
    }

    /// Maps a segment of virtual memory to segments of real memory.
    ///
    /// `func` is invoked with real memory segments of real memory that `virtual_segment` is mapped
    /// to.
    ///
    /// A segment in virtual memory can map to multiple segments of real memory. Here's an example:
    ///
    /// Virtual Memory
    /// ```text
    /// --------------------------------------------------------
    ///          (A) ---------- SEGMENT ---------- (B)
    /// --------------------------------------------------------
    /// ↑               ↑               ↑               ↑
    /// Bucket 0        Bucket 1        Bucket 2        Bucket 3
    /// ```
    ///
    /// The [`VirtualMemory`] is internally divided into fixed-size buckets. In the memory's virtual
    /// address space, all these buckets are consecutive, but in real memory this may not be the case.
    ///
    /// A virtual segment would first be split at the bucket boundaries. The example virtual segment
    /// above would be split into the following segments:
    ///
    ///    (A, end of bucket 0)
    ///    (start of bucket 1, end of bucket 1)
    ///    (start of bucket 2, B)
    ///
    /// Each of the segments above can then be translated into the real address space by looking up
    /// the underlying buckets' addresses in real memory.
    fn for_each_bucket(
        &self,
        MemoryId(id): MemoryId,
        virtual_segment: VirtualSegment,
        bucket_cache: &BucketCache,
        mut func: impl FnMut(RealSegment),
    ) {
        // Get the buckets allocated to the given memory id.
        let buckets = self.memory_buckets[id as usize].as_slice();
        let bucket_size_in_bytes = self.bucket_size_in_bytes().get();

        let virtual_offset = virtual_segment.address.get();

        let mut length = virtual_segment.length.get();
        let mut bucket_idx = (virtual_offset / bucket_size_in_bytes) as usize;
        // The start offset where we start reading from in a bucket. In the first iteration the
        // value is calculated from `virtual_offset`, in later iterations, it's always 0.
        let mut start_offset_in_bucket = virtual_offset % bucket_size_in_bytes;

        while length > 0 {
            let bucket_address =
                self.bucket_address(buckets.get(bucket_idx).expect("bucket idx out of bounds"));

            let bucket_start = bucket_idx as u64 * bucket_size_in_bytes;
            let segment_len = (bucket_size_in_bytes - start_offset_in_bucket).min(length);

            // Cache this bucket.
            bucket_cache.store(
                VirtualSegment {
                    address: bucket_start.into(),
                    length: self.bucket_size_in_bytes(),
                },
                bucket_address,
            );

            func(RealSegment {
                address: bucket_address + start_offset_in_bucket.into(),
                length: segment_len.into(),
            });

            length -= segment_len;
            bucket_idx += 1;
            start_offset_in_bucket = 0;
        }
    }

    fn bucket_size_in_bytes(&self) -> Bytes {
        Bytes::from(self.bucket_size_in_pages as u64 * WASM_PAGE_SIZE)
    }

    /// Returns the number of buckets needed to accommodate the given number of pages.
    fn num_buckets_needed(&self, num_pages: u64) -> u64 {
        // Ceiling division.
        num_pages.div_ceil(self.bucket_size_in_pages as u64)
    }

    /// Returns the underlying memory.
    pub fn into_memory(self) -> M {
        self.memory
    }

    #[inline]
    fn bucket_address(&self, id: &BucketId) -> Address {
        Address::from(BUCKETS_OFFSET_IN_BYTES) + self.bucket_size_in_bytes() * Bytes::from(id.0)
    }
}

#[derive(Copy, Clone)]
struct VirtualSegment {
    address: Address,
    length: Bytes,
}

impl VirtualSegment {
    fn contains_segment(&self, other: &VirtualSegment) -> bool {
        self.address <= other.address && other.address + other.length <= self.address + self.length
    }
}

struct RealSegment {
    address: Address,
    length: Bytes,
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
#[derive(Clone, Copy, Debug, PartialEq)]
struct BucketId(u16);

fn bucket_allocations_address(id: BucketId) -> Address {
    Address::from(0) + Header::size() + Bytes::from(id.0)
}

/// Cache which stores the last touched bucket and the corresponding real address.
///
/// If a segment from this bucket is accessed, we can return the real address faster.
#[derive(Clone)]
struct BucketCache {
    bucket: Cell<VirtualSegment>,
    /// The real address that corresponds to bucket.address
    real_address: Cell<Address>,
}

impl BucketCache {
    #[inline]
    fn new() -> Self {
        BucketCache {
            bucket: Cell::new(VirtualSegment {
                address: Address::from(0),
                length: Bytes::new(0),
            }),
            real_address: Cell::new(Address::from(0)),
        }
    }
}

impl BucketCache {
    /// Returns the real address corresponding to `virtual_segment.address` if `virtual_segment`
    /// is fully contained within the cached bucket, otherwise `None`.
    #[inline]
    fn get(&self, virtual_segment: VirtualSegment) -> Option<Address> {
        let cached_bucket = self.bucket.get();

        cached_bucket
            .contains_segment(&virtual_segment)
            .then(|| self.real_address.get() + (virtual_segment.address - cached_bucket.address))
    }

    /// Stores the mapping of a bucket to a real address.
    #[inline]
    fn store(&self, bucket: VirtualSegment, real_address: Address) {
        self.bucket.set(bucket);
        self.real_address.set(real_address);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::safe_write;
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

        assert_eq!(mem_mgr.inner.borrow().memory_buckets[0], vec![BucketId(0)]);

        assert!(mem_mgr.inner.borrow().memory_buckets[1..]
            .iter()
            .all(|x| x.is_empty()));
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
            &mem_mgr.inner.borrow().memory_buckets[..2],
            &[vec![BucketId(0)], vec![BucketId(1)],]
        );

        assert!(mem_mgr.inner.borrow().memory_buckets[2..]
            .iter()
            .all(|x| x.is_empty()));

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
                write(memory, offset, &data);

                {
                    // Verify the blob can be read back using read.
                    let mut bytes = vec![0; data.len()];
                    memory.read(offset, &mut bytes);
                    assert_eq!(bytes, data);
                }

                {
                    // Verify the blob can be read back using read_to_vec.
                    let mut bytes = vec![];
                    read_to_vec(memory, offset.into(), &mut bytes, data.len());
                    assert_eq!(bytes, data);
                }

                {
                    // Verify the blob can be read back using read_unsafe.
                    let mut bytes = vec![0; data.len()];
                    unsafe {
                        memory.read_unsafe(offset, bytes.as_mut_ptr(), data.len());
                    }
                    assert_eq!(bytes, data);
                }
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

    // Make a few reads and writes and compare the results against golden files that should stay
    // stable between commits.
    // The operations were chosen so that they exercise most of the implementation.
    #[test]
    fn stability() {
        let mem = make_memory();
        let mem_mgr = MemoryManager::init_with_bucket_size(mem.clone(), 1); // very small bucket size.

        let data: Vec<_> = (0u8..=255u8)
            .cycle()
            .take((WASM_PAGE_SIZE * 2 + 901) as usize)
            .collect();

        const MEMORIES: u8 = 3;
        let mut memory_id = 0;
        let mut next_memory = || {
            memory_id += 1;
            memory_id %= MEMORIES;
            mem_mgr.get(MemoryId(memory_id))
        };

        // There are 5 operations
        for _ in 0..MEMORIES * 5 {
            safe_write(&next_memory(), 0, data.as_slice()).unwrap();
            safe_write(&next_memory(), WASM_PAGE_SIZE / 2, data.as_slice()).unwrap();
            safe_write(&next_memory(), WASM_PAGE_SIZE - 1, data.as_slice()).unwrap();
            safe_write(&next_memory(), WASM_PAGE_SIZE + 1, data.as_slice()).unwrap();
            safe_write(
                &next_memory(),
                2 * WASM_PAGE_SIZE + WASM_PAGE_SIZE / 2,
                data.as_slice(),
            )
            .unwrap();
        }

        let expected_write = include_bytes!("memory_manager/stability_write.golden");
        assert!(expected_write.as_slice() == mem.borrow().as_slice());

        let mut read = vec![0; 4 * WASM_PAGE_SIZE as usize];

        // There are 4 operations
        for _ in 0..MEMORIES * 4 {
            next_memory().read(0, &mut read[0..WASM_PAGE_SIZE as usize / 2]);
            next_memory().read(
                WASM_PAGE_SIZE / 2 - 150,
                &mut read[WASM_PAGE_SIZE as usize / 2..WASM_PAGE_SIZE as usize],
            );
            next_memory().read(
                WASM_PAGE_SIZE - 473,
                &mut read[WASM_PAGE_SIZE as usize..WASM_PAGE_SIZE as usize * 2],
            );
            next_memory().read(WASM_PAGE_SIZE * 2, &mut read[WASM_PAGE_SIZE as usize * 2..]);
        }

        let expected_read = include_bytes!("memory_manager/stability_read.golden");
        assert!(expected_read.as_slice() == read.as_slice());
    }

    #[test]
    fn bucket_cache() {
        let bucket_cache = BucketCache::new();

        // No match, nothing has been stored.
        assert_eq!(
            bucket_cache.get(VirtualSegment {
                address: Address::from(0),
                length: Bytes::from(1u64)
            }),
            None
        );

        bucket_cache.store(
            VirtualSegment {
                address: Address::from(0),
                length: Bytes::from(335u64),
            },
            Address::from(983),
        );

        // Match at the beginning
        assert_eq!(
            bucket_cache.get(VirtualSegment {
                address: Address::from(1),
                length: Bytes::from(2u64)
            }),
            Some(Address::from(984))
        );

        // Match at the end
        assert_eq!(
            bucket_cache.get(VirtualSegment {
                address: Address::from(334),
                length: Bytes::from(1u64)
            }),
            Some(Address::from(1317))
        );

        // Match entire segment
        assert_eq!(
            bucket_cache.get(VirtualSegment {
                address: Address::from(0),
                length: Bytes::from(335u64),
            }),
            Some(Address::from(983))
        );

        // No match - outside cached segment
        assert_eq!(
            bucket_cache.get(VirtualSegment {
                address: Address::from(1),
                length: Bytes::from(335u64)
            }),
            None
        );
    }
}
