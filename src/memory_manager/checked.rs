//! Checked reopening and growth contracts owned by the memory manager.

use super::*;

/// A manager operation rejected before changing persisted allocation metadata.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemoryManagerError {
    /// The persisted byte order is unsupported.
    UnsupportedByteOrder,
    /// A nonempty backing does not contain a manager.
    ForeignMemory,
    /// The persisted format version is unsupported.
    UnsupportedVersion(u8),
    /// The bucket size must be nonzero.
    ZeroBucketSize,
    /// An explicitly requested bucket size differs from persisted geometry.
    BucketSizeMismatch { requested: u16, observed: u16 },
    /// Reserved bytes are not recognized.
    ReservedHeader,
    /// The bucket count exceeds the table capacity.
    BucketCount(u16),
    /// An allocated bucket is missing, or an unused bucket is assigned.
    BucketTable(u16),
    /// A virtual extent differs from its assigned bucket count.
    VirtualExtent(u8),
    /// The backing does not cover the assigned physical extent.
    TruncatedBacking {
        physical_pages: u64,
        required_pages: u64,
    },
    /// A size calculation overflows its domain.
    ArithmeticOverflow,
    /// Requested growth exceeds the bucket table capacity.
    BucketExhausted { required_buckets: u64 },
    /// Backing growth was refused before assigning any buckets.
    BackingRefused { additional_pages: u64 },
    /// Another operation already holds the manager state.
    ReentrantAccess,
}

impl std::fmt::Display for MemoryManagerError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::UnsupportedByteOrder => "unsupported manager byte order",
            Self::ForeignMemory => "nonempty backing is not a memory manager",
            Self::UnsupportedVersion(_) => "unsupported manager version",
            Self::ZeroBucketSize => "zero manager bucket size",
            Self::BucketSizeMismatch { .. } => "manager bucket size mismatch",
            Self::ReservedHeader => "unrecognized reserved manager bytes",
            Self::BucketCount(_) => "manager bucket count exceeds capacity",
            Self::BucketTable(_) => "invalid manager bucket assignment",
            Self::VirtualExtent(_) => "manager virtual extent disagrees with assigned buckets",
            Self::TruncatedBacking { .. } => "manager backing is truncated",
            Self::ArithmeticOverflow => "manager size calculation overflows",
            Self::BucketExhausted { .. } => "manager bucket table exhausted",
            Self::BackingRefused { .. } => "manager backing growth refused",
            Self::ReentrantAccess => "manager state is already borrowed",
        })
    }
}

impl std::error::Error for MemoryManagerError {}

/// Validated persisted geometry and allocation extents, without memory handles.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MemoryManagerLayout {
    /// Current physical backing extent.
    pub physical_pages: u64,
    /// Persisted bucket size.
    pub bucket_size_in_pages: u16,
    /// Number of assigned buckets.
    pub allocated_buckets: u16,
    /// Virtual page counts indexed by memory ID.
    pub memory_sizes_in_pages: [u64; MAX_NUM_MEMORIES as usize],
    /// Assigned bucket counts indexed by memory ID.
    pub memory_bucket_counts: [u16; MAX_NUM_MEMORIES as usize],
}

// Parse once for checked construction: the validated bucket lists become the
// manager's actual translation state rather than being decoded a second time.
pub(super) fn load_checked<M: Memory>(
    memory: &M,
) -> Result<(MemoryManagerLayout, Vec<Vec<BucketId>>), MemoryManagerError> {
    if cfg!(target_endian = "big") {
        return Err(MemoryManagerError::UnsupportedByteOrder);
    }
    let physical_pages = memory.size();
    physical_pages
        .checked_mul(WASM_PAGE_SIZE)
        .ok_or(MemoryManagerError::ArithmeticOverflow)?;
    if physical_pages == 0 {
        return Err(MemoryManagerError::TruncatedBacking {
            physical_pages,
            required_pages: 1,
        });
    }
    let mut header = [0; 40 + MAX_NUM_MEMORIES as usize * 8];
    memory.read(0, &mut header);
    if &header[..3] != MAGIC {
        return Err(MemoryManagerError::ForeignMemory);
    }
    if header[3] != LAYOUT_VERSION {
        return Err(MemoryManagerError::UnsupportedVersion(header[3]));
    }
    if header[8..40].iter().any(|byte| *byte != 0) {
        return Err(MemoryManagerError::ReservedHeader);
    }
    let allocated_buckets = u16::from_le_bytes([header[4], header[5]]);
    let bucket_size_in_pages = u16::from_le_bytes([header[6], header[7]]);
    if bucket_size_in_pages == 0 {
        return Err(MemoryManagerError::ZeroBucketSize);
    }
    if u64::from(allocated_buckets) > MAX_NUM_BUCKETS {
        return Err(MemoryManagerError::BucketCount(allocated_buckets));
    }
    let required_pages = 1 + u64::from(allocated_buckets) * u64::from(bucket_size_in_pages);
    if physical_pages < required_pages {
        return Err(MemoryManagerError::TruncatedBacking {
            physical_pages,
            required_pages,
        });
    }
    let mut table = vec![];
    read_to_vec(
        memory,
        bucket_allocations_address(BucketId(0)),
        &mut table,
        MAX_NUM_BUCKETS as usize,
    );
    let mut memory_buckets = vec![vec![]; MAX_NUM_MEMORIES as usize];
    let mut memory_bucket_counts = [0; MAX_NUM_MEMORIES as usize];
    for (index, id) in table.into_iter().enumerate() {
        if (index < usize::from(allocated_buckets)) != (id != UNALLOCATED_BUCKET_MARKER) {
            return Err(MemoryManagerError::BucketTable(index as u16));
        }
        if id != UNALLOCATED_BUCKET_MARKER {
            memory_buckets[id as usize].push(BucketId(index as u16));
            memory_bucket_counts[id as usize] += 1;
        }
    }
    let mut memory_sizes_in_pages = [0; MAX_NUM_MEMORIES as usize];
    for (id, pages) in memory_sizes_in_pages.iter_mut().enumerate() {
        let offset = 40 + id * 8;
        *pages = u64::from_le_bytes(header[offset..offset + 8].try_into().unwrap());
        if pages.div_ceil(u64::from(bucket_size_in_pages)) != u64::from(memory_bucket_counts[id]) {
            return Err(MemoryManagerError::VirtualExtent(id as u8));
        }
    }
    Ok((
        MemoryManagerLayout {
            physical_pages,
            bucket_size_in_pages,
            allocated_buckets,
            memory_sizes_in_pages,
            memory_bucket_counts,
        },
        memory_buckets,
    ))
}

impl<M: Memory> MemoryManager<M> {
    /// Initialize an empty backing, or validate and reopen its existing manager.
    /// Never reinitialize nonempty foreign or malformed memory. Backing refusal
    /// on an empty memory performs no writes. Uses default geometry only for a
    /// fresh manager; reopening retains persisted geometry.
    /// Reopening takes O(bucket capacity + memory IDs) work and uses the
    /// validated bucket lists directly as the manager's translation state.
    ///
    /// ```
    /// use ic_stable_structures::{VectorMemory, memory_manager::{MemoryId, MemoryManager}};
    /// let backing = VectorMemory::default();
    /// let manager = MemoryManager::try_init_with_bucket_size(backing.clone(), 2)?;
    /// let memory = manager.get(MemoryId::new(10));
    /// assert_eq!(memory.try_grow(1)?, 0);
    /// assert_eq!(manager.inspect_layout()?.memory_sizes_in_pages[10], 1);
    /// # Ok::<(), ic_stable_structures::memory_manager::MemoryManagerError>(())
    /// ```
    pub fn try_init(memory: M) -> Result<Self, MemoryManagerError> {
        Self::try_init_inner(memory, None)
    }

    /// As [`Self::try_init`], additionally requiring the selected nonzero geometry.
    pub fn try_init_with_bucket_size(
        memory: M,
        bucket_size_in_pages: u16,
    ) -> Result<Self, MemoryManagerError> {
        Self::try_init_inner(memory, Some(bucket_size_in_pages))
    }

    fn try_init_inner(memory: M, selected: Option<u16>) -> Result<Self, MemoryManagerError> {
        if cfg!(target_endian = "big") {
            return Err(MemoryManagerError::UnsupportedByteOrder);
        }
        if selected == Some(0) {
            return Err(MemoryManagerError::ZeroBucketSize);
        }
        let inner = if memory.size() == 0 {
            if memory.grow(1) < 0 {
                return Err(MemoryManagerError::BackingRefused {
                    additional_pages: 1,
                });
            }
            MemoryManagerInner::new(memory, selected.unwrap_or(BUCKET_SIZE_IN_PAGES as u16))
        } else {
            let (layout, memory_buckets) = load_checked(&memory)?;
            if let Some(requested) = selected {
                if requested != layout.bucket_size_in_pages {
                    return Err(MemoryManagerError::BucketSizeMismatch {
                        requested,
                        observed: layout.bucket_size_in_pages,
                    });
                }
            }
            MemoryManagerInner {
                memory,
                allocated_buckets: layout.allocated_buckets,
                bucket_size_in_pages: layout.bucket_size_in_pages,
                memory_sizes_in_pages: layout.memory_sizes_in_pages,
                memory_buckets,
            }
        };
        Ok(Self {
            inner: Rc::new(RefCell::new(inner)),
        })
    }

    /// Validate persisted metadata without changing it or replacing cached state.
    /// The snapshot is diagnostic data; it does not grant memory access.
    /// Takes O(bucket capacity + memory IDs) work, including bounded temporary
    /// translation lists. It does not replace the live manager's cached state.
    pub fn inspect_layout(&self) -> Result<MemoryManagerLayout, MemoryManagerError> {
        let inner = self
            .inner
            .try_borrow()
            .map_err(|_| MemoryManagerError::ReentrantAccess)?;
        load_checked(&inner.memory).map(|(layout, _)| layout)
    }
}

impl<M: Memory> VirtualMemory<M> {
    /// Reserve backing capacity before assigning buckets. Refused growth,
    /// overflow, exhaustion and reentrant access leave manager metadata and
    /// virtual extents unchanged. A zero-page request returns the current size.
    /// Backing implementations must obey [`Memory`]; traps or partial backing
    /// writes are not transactions on native memory.
    /// Work is proportional to newly assigned buckets; zero-page requests
    /// require no backing IO or allocation.
    pub fn try_grow(&self, pages: u64) -> Result<u64, MemoryManagerError> {
        self.memory_manager
            .try_borrow_mut()
            .map_err(|_| MemoryManagerError::ReentrantAccess)?
            .try_grow(self.id, pages)
    }
}

impl<M: Memory> MemoryManagerInner<M> {
    pub(super) fn try_grow(&mut self, id: MemoryId, pages: u64) -> Result<u64, MemoryManagerError> {
        let old_size = self.memory_size(id);
        if pages == 0 {
            return Ok(old_size);
        }
        let new_size = old_size
            .checked_add(pages)
            .ok_or(MemoryManagerError::ArithmeticOverflow)?;
        let additional_buckets =
            self.num_buckets_needed(new_size) - self.num_buckets_needed(old_size);
        let total = additional_buckets
            .checked_add(u64::from(self.allocated_buckets))
            .ok_or(MemoryManagerError::ArithmeticOverflow)?;
        if total > MAX_NUM_BUCKETS {
            return Err(MemoryManagerError::BucketExhausted {
                required_buckets: total,
            });
        }
        let required_pages = 1 + total * u64::from(self.bucket_size_in_pages);
        let physical_pages = self.memory.size();
        if required_pages > physical_pages && self.memory.grow(required_pages - physical_pages) < 0
        {
            return Err(MemoryManagerError::BackingRefused {
                additional_pages: required_pages - physical_pages,
            });
        }
        // All ordinary refusals precede bucket assignment and extent publication.
        let memory_bucket = &mut self.memory_buckets[id.0 as usize];
        memory_bucket.reserve(additional_buckets as usize);
        for _ in 0..additional_buckets {
            let bucket = BucketId(self.allocated_buckets);
            memory_bucket.push(bucket);
            write(
                &self.memory,
                bucket_allocations_address(bucket).get(),
                &[id.0],
            );
            self.allocated_buckets += 1;
        }
        self.memory_sizes_in_pages[id.0 as usize] = new_size;
        self.save_header();
        Ok(old_size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VectorMemory;

    #[derive(Clone, Default)]
    struct RefusingMemory {
        bytes: VectorMemory,
        refuse: Rc<Cell<bool>>,
    }

    impl Memory for RefusingMemory {
        fn size(&self) -> u64 {
            self.bytes.size()
        }
        fn grow(&self, pages: u64) -> i64 {
            if self.refuse.get() {
                -1
            } else {
                self.bytes.grow(pages)
            }
        }
        fn read(&self, offset: u64, dst: &mut [u8]) {
            self.bytes.read(offset, dst);
        }
        fn write(&self, offset: u64, src: &[u8]) {
            self.bytes.write(offset, src);
        }
    }

    #[test]
    fn checked_open_preserves_foreign_and_corrupt_backings() {
        let bytes = VectorMemory::default();
        let manager = MemoryManager::try_init_with_bucket_size(bytes.clone(), 2).unwrap();
        manager.get(MemoryId::new(10)).try_grow(3).unwrap();
        let original = bytes.borrow().clone();
        let cases = [
            (0, 0, MemoryManagerError::ForeignMemory),
            (3, 9, MemoryManagerError::UnsupportedVersion(9)),
            (6, 0, MemoryManagerError::ZeroBucketSize),
            (8, 1, MemoryManagerError::ReservedHeader),
            (4, 1, MemoryManagerError::BucketTable(1)),
            (40 + 10 * 8, 0, MemoryManagerError::VirtualExtent(10)),
            (40 + 255 * 8, 255, MemoryManagerError::BucketTable(0)),
        ];
        for (offset, value, expected) in cases {
            *bytes.borrow_mut() = original.clone();
            bytes.borrow_mut()[offset] = value;
            let before = bytes.borrow().clone();
            assert!(
                matches!(MemoryManager::try_init(bytes.clone()), Err(error) if error == expected)
            );
            assert_eq!(*bytes.borrow(), before);
        }
        *bytes.borrow_mut() = original;
        bytes.borrow_mut().truncate(WASM_PAGE_SIZE as usize);
        assert!(matches!(
            MemoryManager::try_init(bytes.clone()),
            Err(MemoryManagerError::TruncatedBacking {
                physical_pages: 1,
                required_pages: 5
            })
        ));
    }

    #[test]
    fn checked_growth_refusal_and_retry_preserve_assignments() {
        let backing = RefusingMemory::default();
        assert!(matches!(
            MemoryManager::try_init_with_bucket_size(backing.clone(), 0),
            Err(MemoryManagerError::ZeroBucketSize)
        ));
        assert!(backing.bytes.borrow().is_empty());
        backing.refuse.set(true);
        assert!(matches!(
            MemoryManager::try_init(backing.clone()),
            Err(MemoryManagerError::BackingRefused {
                additional_pages: 1
            })
        ));
        assert!(backing.bytes.borrow().is_empty());
        backing.refuse.set(false);
        let manager = MemoryManager::try_init_with_bucket_size(backing.clone(), 2).unwrap();
        let memory = manager.get(MemoryId::new(10));
        backing.refuse.set(true);
        let before = backing.bytes.borrow().clone();
        assert_eq!(
            memory.try_grow(1),
            Err(MemoryManagerError::BackingRefused {
                additional_pages: 2
            })
        );
        assert_eq!(memory.grow(1), -1);
        assert_eq!(memory.size(), 0);
        assert_eq!(*backing.bytes.borrow(), before);
        backing.refuse.set(false);
        assert_eq!(memory.try_grow(3), Ok(0));
        memory.write(0, b"kept");
        assert_eq!(
            memory.try_grow(u64::MAX),
            Err(MemoryManagerError::ArithmeticOverflow)
        );
        assert!(matches!(
            memory.try_grow(32768 * 2),
            Err(MemoryManagerError::BucketExhausted { .. })
        ));
        assert_eq!(memory.try_grow(0), Ok(3));
        drop(memory);
        drop(manager);
        let reopened = MemoryManager::try_init(backing.clone()).unwrap();
        let snapshot = reopened.inspect_layout().unwrap();
        assert_eq!(snapshot.memory_sizes_in_pages[10], 3);
        assert_eq!(snapshot.memory_bucket_counts[10], 2);
        let mut value = [0; 4];
        reopened.get(MemoryId::new(10)).read(0, &mut value);
        assert_eq!(&value, b"kept");
        assert!(matches!(
            MemoryManager::try_init_with_bucket_size(backing, 1),
            Err(MemoryManagerError::BucketSizeMismatch {
                requested: 1,
                observed: 2
            })
        ));
    }

    #[test]
    fn shared_handles_refuse_reentrant_growth_without_effects() {
        let backing = VectorMemory::default();
        let manager = MemoryManager::try_init(backing.clone()).unwrap();
        let memory = manager.get(MemoryId::new(10));
        let before = backing.borrow().clone();
        let guard = manager.inner.borrow_mut();
        assert_eq!(memory.try_grow(0), Err(MemoryManagerError::ReentrantAccess));
        assert_eq!(memory.try_grow(1), Err(MemoryManagerError::ReentrantAccess));
        assert_eq!(*backing.borrow(), before);
        drop(guard);
        assert_eq!(memory.clone().try_grow(1), Ok(0));
        assert_eq!(memory.size(), 1);
    }
}
