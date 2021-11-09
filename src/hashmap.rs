use crate::allocator::{AllocError, Allocator};
use crate::{read_u32, Memory};
use ahash::RandomState;
use std::sync::Arc;

pub const LAYOUT_VERSION: u8 = 1;

#[derive(Debug, PartialEq, Eq)]
pub enum LoadError {
    MemoryEmpty,
    BadMagic([u8; 3]),
    UnsupportedVersion(u8),
}

/*
struct Stable<T> {
    ptr: u32,
    phantom: PhantomData<T> // Do we need this?
}

impl<T> Stable<T> {
    fn new(addr: u32) -> Self {
        Self {
            ptr: addr,
            phantom: PhantomData::<T>
        }
    }

    fn modify(s: Stable<T>,
}*/

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
// #[repr(packed)]
#[derive(Debug, PartialEq)]
struct Header {
    magic: [u8; 3],
    version: u8,
    num_buckets: u32,
}

pub struct HashMap<M: Memory, A: Allocator> {
    allocator: Arc<A>,
    memory: M,
    num_buckets: u32,
    buckets_offset: u32,
    hasher: RandomState,
    pub own_address: u32,
}

impl<M: Clone + Memory, A: Allocator> HashMap<M, A> {
    pub fn new(allocator: Arc<A>, memory: M, num_keys: u32) -> Result<Self, AllocError> {
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

        let hash_map_address = allocator.allocate_zeroed(size_needed).unwrap();

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

    pub fn load(allocator: Arc<A>, memory: M, address: u32) -> Result<Self, LoadError> {
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
        let bucket = self.compute_bucket(key);

        let bucket_header = self.own_address + self.buckets_offset + bucket * 4;
        let mut parent_addr = self.own_address + self.buckets_offset + bucket * 4;
        let mut node_addr = read_u32(&self.memory, parent_addr);

        while node_addr != 0 {
            let node = Entry::load(node_addr, self.memory.clone());

            // Does the key already exist?
            if node.key() == key {
                let e = RawEntry {
                    size: (key.len() + value.len()) as u32,
                    value_offset: key.len() as u32,
                    next: node.next(),
                };

                let new_entry_address = self.write_entry(e, key, value);

                // Update the bucket pointer.
                if parent_addr == bucket_header {
                    // TODO: write_u32 method?
                    self.memory
                        .write(parent_addr, &new_entry_address.to_le_bytes());
                } else {
                    // parent is a node.
                    let mut parent_node = Entry::load(parent_addr, self.memory.clone());
                    parent_node.entry.next = new_entry_address;
                    parent_node.save();
                }

                self.allocator.deallocate(node_addr, node.entry.size);
                return;
            }

            // Traverse.
            parent_addr = node_addr;
            node_addr = node.entry.next;
        }

        // Reached tail of list.
        let e = RawEntry {
            size: (key.len() + value.len()) as u32,
            value_offset: key.len() as u32,
            next: 0,
        };

        let new_entry_address = self.write_entry(e, key, value);

        // Update entry pointer
        if parent_addr == bucket_header {
            self.memory
                .write(parent_addr, &new_entry_address.to_le_bytes());
        } else {
            let mut parent_node = Entry::load(parent_addr, self.memory.clone());
            parent_node.entry.next = new_entry_address;
            parent_node.save();
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
            .allocate((entry_slice.len() + key.len() + value.len()) as u32)
            .unwrap();

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

        let mut entry = Entry::load(entry_address, self.memory.clone());

        while entry.key() != key {
            if entry.entry.next != 0 {
                // traverse the list
                entry_address = entry.entry.next;
                entry = Entry::load(entry_address, self.memory.clone());
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
            let node = Entry::load(node_addr, self.memory.clone());

            // Does the key already exist?
            if node.key() == key {
                let val = node.value();

                // Update the bucket pointer.
                if parent_addr == bucket_header {
                    // TODO: write_u32 method?
                    self.memory
                        .write(parent_addr, &node.entry.next.to_le_bytes());
                } else {
                    // parent is a node.
                    let mut parent_node = Entry::load(parent_addr, self.memory.clone());
                    parent_node.entry.next = node.next();
                    parent_node.save();
                }

                self.allocator.deallocate(node_addr, node.entry.size);
                return Some(val);
            }

            // Traverse.
            parent_addr = node_addr;
            node_addr = node.entry.next;
        }

        // Key not found.
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{allocator::dumb_allocator::DumbAllocator, read_root_data, write_root_data};
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
            let map =
                HashMap::new(Arc::new(allocator), mem.clone(), i).expect("failed to create map");

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
    fn insert_get_single_bucket() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
    }

    #[test]
    fn insert_get_multiple_buckets() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
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
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 10).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        map.insert(&[2], &[4, 5, 6]);

        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4, 5, 6]));

        let map_addr = map.own_address;
        std::mem::drop(map);

        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let map = HashMap::load(Arc::new(allocator), mem.clone(), map_addr)
            .expect("failed to create map");
        assert_eq!(map.get(&[1]), Some(vec![1, 2, 3]));
        assert_eq!(map.get(&[2]), Some(vec![4, 5, 6]));
    }

    #[test]
    fn insert_collision() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
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
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let map = HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        assert_eq!(map.get(&[1]), None);
    }

    #[test]
    fn get_not_found_non_empty_bucket() {
        let mem = make_memory();
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
        let mut map =
            HashMap::new(Arc::new(allocator), mem.clone(), 1).expect("failed to create map");
        map.insert(&[1], &[1, 2, 3]);
        assert_eq!(map.get(&[2]), None);
    }

    #[test]
    fn multiple_hash_maps() {
        let mem = make_memory();
        let allocator = Arc::new(DumbAllocator::new(mem.clone()).unwrap());
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
        let allocator = Arc::new(DumbAllocator::new(mem.clone()).unwrap());
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
        let allocator = Arc::new(DumbAllocator::load(mem.clone()).unwrap());

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
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
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
        let allocator = DumbAllocator::new(mem.clone()).unwrap();
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
