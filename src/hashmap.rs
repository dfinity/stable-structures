use crate::{read_u32, Memory};
use ahash::RandomState;
use std::sync::Arc;

pub const LAYOUT_VERSION: u8 = 1;

/*
struct Pointer<M: Memory> {
    addr: u32,
    memory: Arc<M>
}

impl<M: Memory> Pointer<M> {
    fn write(&self, data: &[u8]) {
        self.memory.write(self.addr, data);
    }

    fn write_with_offset(&self, offset: u32, data: &[u8]) {
        self.memory.write(self.addr + offset, data);
    }
}*/

pub trait Allocator {
    /// Allocates a piece of memory with the given size, and return its pointer.
    // TODO: add layout?
    fn allocate(&self, size: u32) -> u32;
    // TODO: free
}

struct DumbAllocator<M: Memory> {
    memory: M,
}

struct DumbAllocatorHeader {
    magic: [u8; 3],
    version: u8,
    free_offset: u32,
}

impl<M: Memory> DumbAllocator<M> {
    fn new(memory: M) -> Result<Self, AllocError> {
        if memory.size() < 1 && memory.grow(1) == -1 {
            return Err(AllocError::GrowFailed {
                current: 0,
                delta: 1,
            });
        }

        let header_len = core::mem::size_of::<DumbAllocatorHeader>() as u32;

        let header = DumbAllocatorHeader {
            magic: *b"DAL",
            version: 0,
            free_offset: header_len, // beginning of free space.
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<DumbAllocatorHeader>(),
            )
        };

        memory.write(0, header_slice);

        Ok(Self { memory })
    }

    fn get_free_offset(&self) -> u32 {
        let mut header: DumbAllocatorHeader = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<DumbAllocatorHeader>(),
            )
        };
        self.memory.read(0, header_slice);
        header.free_offset
    }

    fn set_free_offset(&self, new_free_offset: u32) {
        let mut header: DumbAllocatorHeader = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<DumbAllocatorHeader>(),
            )
        };
        self.memory.read(0, header_slice);
        header.free_offset = new_free_offset;
        self.memory.write(0, header_slice);
    }
}

impl<M: Memory> Allocator for DumbAllocator<M> {
    fn allocate(&self, size: u32) -> u32 {
        // TODO: grow memory if needed.

        let old_free_offset = self.get_free_offset();

        self.set_free_offset(old_free_offset + size);

        old_free_offset
    }
}

// TODO: copied from log.rs
#[derive(Debug, PartialEq, Eq)]
pub enum AllocError {
    GrowFailed { current: u32, delta: u32 },
    AddressSpaceOverflow,
}

#[derive(Debug, PartialEq, Eq)]
pub enum LoadError {
    MemoryEmpty,
    BadMagic([u8; 3]),
    UnsupportedVersion(u8),
}

struct Entry<M: Memory> {
    entry: RawEntry,
    entry_address: u32,
    memory: M,
}

impl<M: Memory> Entry<M> {
    fn load(address: u32, memory: M) -> Self {
        let mut entry: RawEntry = unsafe { core::mem::zeroed() };
        let entry_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut entry as *mut _ as *mut u8,
                core::mem::size_of::<RawEntry>(),
            )
        };
        memory.read(address, entry_slice);

        Self {
            entry,
            entry_address: address,
            memory,
        }
    }

    fn save(&self) {
        let entry_slice = unsafe {
            core::slice::from_raw_parts(
                &self.entry as *const _ as *const u8,
                core::mem::size_of::<RawEntry>(),
            )
        };

        self.memory.write(self.entry_address, entry_slice);
    }

    fn key(&self) -> Vec<u8> {
        let entry_len = core::mem::size_of::<RawEntry>() as u32;
        let key_len = self.entry.value_offset;
        let mut key = vec![0; key_len as usize];
        self.memory.read(self.entry_address + entry_len, &mut key);
        key
    }

    fn value(&self) -> Vec<u8> {
        let entry_len = core::mem::size_of::<RawEntry>() as u32;
        let value_len = self.entry.size - self.entry.value_offset;
        let mut val = vec![0; value_len as usize];
        self.memory.read(
            self.entry_address + entry_len + self.entry.value_offset,
            &mut val,
        );
        val
    }

    fn next(&self) -> u32 {
        self.entry.next
    }
}

#[derive(Debug, PartialEq)]
struct RawEntry {
    size: u32,
    value_offset: u32,
    next: u32, // Pointer to next entry in bucket.
}

// TODO: make struct use u64
#[derive(Debug, PartialEq)]
struct Header {
    magic: [u8; 3],
    version: u8,
    num_buckets: u32,
}

pub struct HashMap<M: Memory, A: Allocator> {
    allocator: A,
    memory: M,
    num_buckets: u32,
    buckets_offset: u32,
    hasher: RandomState,
    own_address: u32,
}

impl<M: Clone + Memory, A: Allocator> HashMap<M, A> {
    pub fn new(allocator: A, memory: M, num_keys: u32) -> Result<Self, AllocError> {
        let header_len = core::mem::size_of::<Header>() as u32;

        // For now, assume number of buckets = number of keys
        let num_buckets = num_keys;

        // Each bucket is a 32-bit pointer.
        let index_len = num_buckets
            .checked_mul(std::mem::size_of::<u32>() as u32)
            .ok_or(AllocError::AddressSpaceOverflow)?;

        let header = Header {
            magic: *b"HMP",
            version: LAYOUT_VERSION,
            num_buckets,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<Header>(),
            )
        };

        let size_needed = header_len + index_len;

        let hash_map_address = allocator.allocate(size_needed);

        memory.write(hash_map_address, header_slice);

        Ok(Self {
            allocator,
            memory,
            num_buckets,
            buckets_offset: header_len,
            // Setting seeds to be deterministic
            hasher: RandomState::with_seeds(0, 0, 0, 0),
            own_address: hash_map_address,
        })
    }

    pub fn load(allocator: A, memory: M, address: u32) -> Result<Self, LoadError> {
        let mut header: Header = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<Header>(),
            )
        };
        if memory.size() == 0 {
            return Err(LoadError::MemoryEmpty);
        }
        memory.read(address, header_slice);
        if &header.magic != b"HMP" {
            return Err(LoadError::BadMagic(header.magic));
        }
        if header.version != LAYOUT_VERSION {
            return Err(LoadError::UnsupportedVersion(header.version));
        }
        let buckets_offset = core::mem::size_of::<Header>() as u32;
        Ok(Self {
            allocator,
            memory,
            num_buckets: header.num_buckets,
            buckets_offset,
            hasher: RandomState::with_seeds(0, 0, 0, 0),
            own_address: address,
        })
    }

    pub fn insert(&mut self, key: &[u8], value: &[u8]) {
        let bucket = self.get_bucket(key);

        let mut entry_address = read_u32(
            &self.memory,
            self.own_address + self.buckets_offset + bucket,
        );

        if entry_address == 0 {
            // Bucket list is empty. Add new entry here.
            let e = RawEntry {
                size: (key.len() + value.len()) as u32,
                value_offset: key.len() as u32,
                next: 0,
            };

            let new_entry_address = self.write_entry(e, key, value);

            // Update bucket pointer
            self.memory.write(
                self.own_address + self.buckets_offset + bucket,
                &new_entry_address.to_le_bytes(),
            );
        } else {
            // Traverse the list.
            let mut entry = Entry::load(entry_address, self.memory.clone());
            while entry.next() != 0 {
                entry_address = entry.next();
                entry = Entry::load(entry_address, self.memory.clone());
            }

            // Reached tail of list.
            let e = RawEntry {
                size: (key.len() + value.len()) as u32,
                value_offset: key.len() as u32,
                next: 0,
            };

            let new_entry_address = self.write_entry(e, key, value);

            // Update entry pointer
            entry.entry.next = new_entry_address;
            entry.save();
        }
    }

    fn write_entry(&mut self, entry: RawEntry, key: &[u8], value: &[u8]) -> u32 {
        let entry_slice = unsafe {
            // TODO: look up the docs of this.
            core::slice::from_raw_parts(
                &entry as *const _ as *const u8,
                core::mem::size_of::<RawEntry>(),
            )
        };

        let entry_address = self
            .allocator
            .allocate((entry_slice.len() + key.len() + value.len()) as u32);

        self.memory.write(entry_address, entry_slice);

        // Write the key and value pair immediately afterwards.
        self.memory
            .write(entry_address + entry_slice.len() as u32, key);
        self.memory.write(
            entry_address + entry_slice.len() as u32 + key.len() as u32,
            value,
        );

        entry_address
    }

    fn get_bucket(&self, key: &[u8]) -> u32 {
        use core::hash::{BuildHasher, Hash, Hasher};
        let mut state = self.hasher.build_hasher();
        key.hash(&mut state);
        (state.finish() as u32) % self.num_buckets
    }

    pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        // Compute bucket.
        let bucket = self.get_bucket(key);

        // Read entry.
        let mut entry_address = read_u32(
            &self.memory,
            self.own_address + self.buckets_offset + bucket,
        );

        // FIXME: are we guaranteed that the address is zero?
        // Maybe we need to ensure that by initializing them.
        if entry_address == 0 {
            // Bucket is empty
            return None;
        }

        let mut entry = Entry::load(entry_address, self.memory.clone());

        while &entry.key() != key {
            if entry.entry.next != 0 {
                // traverse the list
                entry_address = entry.entry.next;
                entry = Entry::load(entry_address, self.memory.clone());
            } else {
                return None;
            }
        }

        return Some(entry.value());
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use core::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn initialization() {
        for i in 1..10 {
            let mem = make_memory();
            let allocator = DumbAllocator::new(mem.clone()).unwrap();
            let map = HashMap::new(allocator, mem.clone(), i).expect("failed to create map");

            let mut header: Header = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<Header>(),
                )
            };
            mem.read(map.own_address, header_slice);

            assert_eq!(
                header,
                Header {
                    magic: *b"HMP",
                    version: 1,
                    num_buckets: i,
                }
            );

            // The bucket pointers are initialized correctly.
            for bucket_index in 0..i {
                assert_eq!(
                    read_u32(
                        &mem,
                        map.own_address + map.buckets_offset + bucket_index * 4
                    ),
                    0
                );
            }
        }
    }

    #[test]
    fn insert_get() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map = HashMap::new(allocator, mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
    }

    #[test]
    fn dropping_then_loading_preserves_data() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map = HashMap::new(allocator, mem.clone(), 10).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        map.insert(&[2], &[4, 5, 6]);

        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4, 5, 6]));

        let map_addr = map.own_address;
        std::mem::drop(map);

        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::load(allocator, mem.clone(), map_addr).expect("failed to create map");
        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4, 5, 6]));
    }

    #[test]
    fn insert_collision() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map = HashMap::new(allocator, mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        map.insert(&[2], &[4, 5, 6]);
        map.insert(&[3], &[7, 8]);
        map.insert(&[4], &[9, 10, 11, 12]);

        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4, 5, 6]));
        assert_eq!(map.get(&[3]), Some(vec![7, 8]));
        assert_eq!(map.get(&[4]), Some(vec![9, 10, 11, 12]));
    }

    #[test]
    fn get_not_found_empty_bucket() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let map = HashMap::new(allocator, mem.clone(), 1).expect("failed to create map");
        assert_eq!(map.get(&[1]), None);
    }

    #[test]
    fn get_not_found_non_empty_bucket() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map = HashMap::new(allocator, mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        assert_eq!(map.get(&[2]), None);
    }
}
