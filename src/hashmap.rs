use crate::allocator::{AllocError, Allocator};
use crate::{read_u32, write_u32, Memory};
use ahash::RandomState;
use std::sync::Arc;

pub const LAYOUT_VERSION: u8 = 1;

#[derive(Debug, PartialEq, Eq)]
pub enum LoadError {
    MemoryEmpty,
    BadMagic([u8; 3]),
    UnsupportedVersion(u8),
}

#[repr(packed)]
#[derive(Debug, PartialEq, Clone, Copy)]
struct HashMapHeader {
    magic: [u8; 3],
    version: u8,
    num_buckets: u32,
}

// A header that is placed before a (key, value).
#[repr(packed)]
struct EntryHeader {
    // The offset where the value begins in memory
    key_size: u32,

    // The size of key + value.
    value_size: u32,

    // Pointer to the next entry.
    next: u32,
}

/// A "stable" hash map that can handle keys/values of arbitrary size.
///
/// The hash map is initialized with a number of buckets. Keys are mapped to
/// a single bucket, and a linked list is created for each bucket to handle
/// collisions.
///
/// The hash map is "stable" in the sense that it stores all its data in the
/// given memory and can be loaded in O(1) time from that memory.
pub struct HashMap<M: Memory, A: Allocator> {
    allocator: Arc<A>,
    memory: M,
    num_buckets: u32,
    buckets_offset: u32,
    hasher: RandomState,
    pub own_address: u32,
}

impl<M: Memory, A: Allocator> HashMap<M, A> {
    pub fn new(allocator: Arc<A>, memory: M, num_buckets: u32) -> Result<Self, AllocError> {
        let header_len = core::mem::size_of::<HashMapHeader>() as u32;

        // Each bucket is a 32-bit pointer.
        let index_len = num_buckets
            .checked_mul(std::mem::size_of::<u32>() as u32)
            .ok_or(AllocError::AddressSpaceOverflow)?;

        let header = HashMapHeader {
            magic: *b"HMP",
            version: LAYOUT_VERSION,
            num_buckets,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<HashMapHeader>(),
            )
        };

        let size_needed = header_len + index_len;

        let hash_map_address = allocator.allocate_zeroed(size_needed).unwrap();

        memory.write(hash_map_address, header_slice);

        Ok(Self {
            allocator,
            memory,
            num_buckets,
            buckets_offset: header_len,
            // Setting seeds to be deterministic.
            // We can randomize these seeds if we want to be HashDos resistant.
            hasher: RandomState::with_seeds(0, 0, 0, 0),
            own_address: hash_map_address,
        })
    }

    pub fn load(allocator: Arc<A>, memory: M, address: u32) -> Result<Self, LoadError> {
        let mut header: HashMapHeader = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<HashMapHeader>(),
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
        let buckets_offset = core::mem::size_of::<HashMapHeader>() as u32;
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
        let bucket = self.compute_bucket(key);

        let bucket_header = self.own_address + self.buckets_offset + bucket * 4;
        let mut parent_addr = self.own_address + self.buckets_offset + bucket * 4;
        let mut node_addr = read_u32(&self.memory, parent_addr);

        while node_addr != 0 {
            let node = Entry::load(node_addr, &self.memory);

            // Does the key already exist?
            if node.key() == key {
                let e = EntryHeader {
                    key_size: key.len() as u32,
                    value_size: value.len() as u32,
                    next: node.header.next,
                };

                let new_entry = Entry::new(e, key, value, &self.memory, &*self.allocator);

                // Update the bucket pointer.
                if parent_addr == bucket_header {
                    write_u32(&self.memory, parent_addr, new_entry.address);
                } else {
                    // parent is a node.
                    let mut parent_node = Entry::load(parent_addr, &self.memory);
                    parent_node.header.next = new_entry.address;
                    parent_node.save();
                }

                self.allocator.deallocate(node_addr, node.size());
                return;
            }

            // Traverse.
            parent_addr = node_addr;
            node_addr = node.header.next;
        }

        // Reached tail of list.
        let e = EntryHeader {
            key_size: key.len() as u32,
            value_size: value.len() as u32,
            next: 0,
        };

        let new_entry = Entry::new(e, key, value, &self.memory, &*self.allocator);

        // Update entry pointer
        if parent_addr == bucket_header {
            write_u32(&self.memory, parent_addr, new_entry.address);
        } else {
            let mut parent_node = Entry::load(parent_addr, &self.memory);
            parent_node.header.next = new_entry.address;
            parent_node.save();
        }
    }

    // Computes the bucket the key should be placed in.
    fn compute_bucket(&self, key: &[u8]) -> u32 {
        use core::hash::{BuildHasher, Hash, Hasher};
        let mut state = self.hasher.build_hasher();
        key.hash(&mut state);
        (state.finish() as u32) % self.num_buckets
    }

    pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        // Compute bucket.
        let bucket = self.compute_bucket(key);

        // Read entry.
        let mut entry_address = read_u32(
            &self.memory,
            self.own_address + self.buckets_offset + bucket * 4,
        );

        if entry_address == 0 {
            // Bucket is empty
            return None;
        }

        let mut entry = Entry::load(entry_address, &self.memory);

        while entry.key() != key {
            if entry.header.next != 0 {
                // traverse the list
                entry_address = entry.header.next;
                entry = Entry::load(entry_address, &self.memory);
            } else {
                return None;
            }
        }

        Some(entry.value())
    }

    pub fn remove(&mut self, key: &[u8]) -> Option<Vec<u8>> {
        let bucket = self.compute_bucket(key);

        let bucket_header = self.own_address + self.buckets_offset + bucket * 4;
        let mut parent_addr = self.own_address + self.buckets_offset + bucket * 4;
        let mut node_addr = read_u32(&self.memory, parent_addr);

        while node_addr != 0 {
            let node = Entry::load(node_addr, &self.memory);

            // Does the key already exist?
            if node.key() == key {
                let val = node.value();

                // Update the bucket pointer.
                if parent_addr == bucket_header {
                    write_u32(&self.memory, parent_addr, node.header.next);
                } else {
                    // parent is a node.
                    let mut parent_node = Entry::load(parent_addr, &self.memory);
                    parent_node.header.next = node.header.next;
                    parent_node.save();
                }

                self.allocator.deallocate(node_addr, node.size());
                return Some(val);
            }

            // Traverse.
            parent_addr = node_addr;
            node_addr = node.header.next;
        }

        // Key not found.
        None
    }
}

// A wrapper around an entry in the hashmap.
struct Entry<'a, M: Memory> {
    header: EntryHeader,
    address: u32,
    memory: &'a M,
}

impl<'a, M: Memory> Entry<'a, M> {
    // Creates and allocates a new entry.
    fn new<A: Allocator>(
        header: EntryHeader,
        key: &[u8],
        value: &[u8],
        memory: &'a M,
        allocator: &A,
    ) -> Self {
        let entry_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<EntryHeader>(),
            )
        };

        // Allocate the entry in memory.
        let address = allocator
            .allocate((entry_slice.len() + key.len() + value.len()) as u32)
            .unwrap();

        // Write the entry, key, and value in sequence.
        memory.write(address, entry_slice);
        memory.write(address + entry_slice.len() as u32, key);
        memory.write(address + entry_slice.len() as u32 + key.len() as u32, value);

        Self {
            header,
            address,
            memory,
        }
    }

    fn load(address: u32, memory: &'a M) -> Self {
        let mut header: EntryHeader = unsafe { core::mem::zeroed() };
        let entry_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<EntryHeader>(),
            )
        };
        memory.read(address, entry_slice);

        Self {
            header,
            address,
            memory,
        }
    }

    fn save(&self) {
        let entry_slice = unsafe {
            core::slice::from_raw_parts(
                &self.header as *const _ as *const u8,
                core::mem::size_of::<EntryHeader>(),
            )
        };

        self.memory.write(self.address, entry_slice);
    }

    fn key(&self) -> Vec<u8> {
        let entry_len = core::mem::size_of::<EntryHeader>() as u32;
        let key_len = self.header.key_size;
        let mut key = vec![0; key_len as usize];
        self.memory.read(self.address + entry_len, &mut key);
        key
    }

    fn value(&self) -> Vec<u8> {
        let entry_len = core::mem::size_of::<EntryHeader>() as u32;
        let value_len = self.header.value_size;
        let mut val = vec![0; value_len as usize];
        self.memory
            .read(self.address + entry_len + self.header.key_size, &mut val);
        val
    }

    fn size(&self) -> u32 {
        self.header.key_size + self.header.value_size + core::mem::size_of::<EntryHeader>() as u32
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{allocator::mock_allocator::MockAllocator, read_root_data, write_root_data};
    use core::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn initialization() {
        for i in 1..10 {
            let mem = make_memory();
            let allocator = MockAllocator::new(mem.clone()).unwrap();
            let map =
                HashMap::new(Arc::new(allocator), mem.clone(), i).expect("failed to create map");

            let mut header: HashMapHeader = unsafe { core::mem::zeroed() };
            let header_slice = unsafe {
                core::slice::from_raw_parts_mut(
                    &mut header as *mut _ as *mut u8,
                    core::mem::size_of::<HashMapHeader>(),
                )
            };
            mem.read(map.own_address, header_slice);

            assert_eq!(
                header,
                HashMapHeader {
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
    fn insert_get_single_bucket() {
        let mem = make_memory();
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
    }

    #[test]
    fn insert_get_multiple_buckets() {
        let mem = make_memory();
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 10).expect("failed to create map");

        for i in 0..10 {
            map.insert(&[i], &[i, i + 1, i + 2]);
        }

        for i in 0..10 {
            assert_eq!(map.get(&[i]), Some(vec![i, i + 1, i + 2]));
        }
    }

    #[test]
    fn dropping_then_loading_preserves_data() {
        let mem = make_memory();
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 10).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        map.insert(&[2], &[4, 5, 6]);

        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4, 5, 6]));

        let map_addr = map.own_address;
        std::mem::drop(map);

        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let map = HashMap::load(Arc::new(allocator), mem.clone(), map_addr)
            .expect("failed to create map");
        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4, 5, 6]));
    }

    #[test]
    fn insert_collision() {
        let mem = make_memory();
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
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
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let map = HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        assert_eq!(map.get(&[1]), None);
    }

    #[test]
    fn get_not_found_non_empty_bucket() {
        let mem = make_memory();
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        assert_eq!(map.get(&[2]), None);
    }

    #[test]
    fn multiple_hash_maps() {
        let mem = make_memory();
        let allocator = Arc::new(MockAllocator::new(mem.clone()).unwrap());
        let mut map1 =
            HashMap::new(allocator.clone(), mem.clone(), 1).expect("failed to create map");
        map1.insert(&[1], &[1, 2, 3]);

        let mut map2 = HashMap::new(allocator, mem.clone(), 1).expect("failed to create map");
        map2.insert(&[1], &[4, 5, 6]);

        assert_eq!(map1.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map2.get(&[1]), Some(vec![4, 5, 6]));
    }

    #[test]
    fn load_multiple_hash_maps() {
        let mem = make_memory();
        let allocator = Arc::new(MockAllocator::new(mem.clone()).unwrap());
        let mut map1 =
            HashMap::new(allocator.clone(), mem.clone(), 1).expect("failed to create map");
        map1.insert(&[1], &[1, 2, 3]);

        let mut map2 =
            HashMap::new(allocator.clone(), mem.clone(), 1).expect("failed to create map");
        map2.insert(&[1], &[4, 5, 6]);

        assert_eq!(map1.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map2.get(&[1]), Some(vec![4, 5, 6]));

        let root_data: Vec<u8> = [map1.own_address, map2.own_address]
            .iter()
            .map(|m| m.to_le_bytes().to_vec())
            .flatten()
            .collect();

        write_root_data(&mem, &*allocator, &root_data);

        std::mem::drop(map1);
        std::mem::drop(map2);
        std::mem::drop(allocator);
        std::mem::drop(root_data);

        let root_data = read_root_data(&mem).unwrap();
        let allocator = Arc::new(MockAllocator::load(mem.clone()).unwrap());

        use std::convert::TryInto;
        let map1_index = u32::from_le_bytes(root_data[0..4].try_into().unwrap());
        let map2_index = u32::from_le_bytes(root_data[4..8].try_into().unwrap());

        let map1 = HashMap::load(allocator.clone(), mem.clone(), map1_index)
            .expect("failed to create map");
        let map2 = HashMap::load(allocator, mem.clone(), map2_index).expect("failed to create map");
        assert_eq!(map1.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map2.get(&[1]), Some(vec![4, 5, 6]));
    }

    #[test]
    fn overwrite_key() {
        let mem = make_memory();
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        map.insert(&[2], &[4]);
        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4]));
        map.insert(&[1], &[4, 5]);
        assert_eq!(map.get(&[1]), Some(vec![4, 5]));
        assert_eq!(map.get(&[2]), Some(vec![4]));
        map.insert(&[1], &[6, 7, 8]);
        assert_eq!(map.get(&[1]), Some(vec![6, 7, 8]));
        assert_eq!(map.get(&[2]), Some(vec![4]));
    }

    #[test]
    fn remove() {
        let mem = make_memory();
        let allocator = MockAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        assert_eq!(map.remove(&[1]), None);
        map.insert(&[1], &[1, 2, 3]);
        map.insert(&[2], &[4]);
        assert_eq!(map.remove(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[1]), None);
        assert_eq!(map.remove(&[2]), Some(vec![4]));
        assert_eq!(map.get(&[2]), None);
    }
}
