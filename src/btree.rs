use crate::{Memory64, WASM_PAGE_SIZE};
//mod node;
//use crate::btree::node;

const LAYOUT_VERSION: u8 = 1;
const NULL: u64 = 0;

const MAX_KEY_SIZE: u32 = 64;
const MAX_VALUE_SIZE: u32 = 64;

// Taken from `BTreeMap`.
const B: u64 = 6;
const CAPACITY: u64 = 2 * B - 1;

const LEAF_NODE_TYPE: u8 = 0;
const INTERNAL_NODE_TYPE: u8 = 1;

type Ptr = u64;

#[repr(packed)]
#[derive(Debug, PartialEq, Clone, Copy)]
struct Header {
    magic: [u8; 3],
    version: u8,
    root_offset: u64,
    free_list: u64,
    //max_key_size: u32,
    //max_value_size: u32, // TODO: extend this to be aligned with 8-bytes?
}

pub enum LoadError {
    MemoryEmpty,
    BadMagic([u8; 3]),
    UnsupportedVersion(u8),
}

#[derive(Debug, PartialEq, Eq)]
pub enum WriteError {
    IndexFull(u32),
    GrowFailed { current: u64, delta: u64 },
    AddressSpaceOverflow,
}

pub struct StableBTreeMap<M: Memory64> {
    memory: M,
    root_offset: Ptr,
    free_list: Ptr,
    //max_key_size: u32,
    //max_value_size: u32,
    //root: Node,
}

type Key = Vec<u8>;
type Value = Vec<u8>;

#[derive(Debug, PartialEq)]
struct LeafNode {
    address: Ptr,
    keys: Vec<Key>,
    values: Vec<Value>,
}

impl LeafNode {
    fn new(address: u64) -> Self {
        LeafNode {
            address,
            keys: vec![],
            values: vec![],
        }
    }

    fn is_full(&self) -> bool {
        self.keys.len() >= CAPACITY as usize
    }

    fn save(&self, memory: &impl Memory64) -> Result<(), WriteError> {
        println!("saving node at address {:?}", self.address);
        let header = NodeHeader {
            node_type: LEAF_NODE_TYPE,
            num_entries: self.values.len() as u64,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<NodeHeader>(),
            )
        };

        let header_len = core::mem::size_of::<NodeHeader>() as u64;

        write(memory, self.address, header_slice)?;

        let mut offset = header_len;
        // Write the entries.
        for (key, value) in self.keys.iter().zip(self.values.iter()) {
            // Write the size of the key.
            write(
                memory,
                self.address + offset,
                &(key.len() as u32).to_le_bytes(),
            )?;
            offset += 4;
            write(memory, self.address + offset, &key)?;
            offset += MAX_KEY_SIZE as u64;
            write(
                memory,
                self.address + offset,
                &(value.len() as u32).to_le_bytes(),
            )?;
            offset += 4;
            write(memory, self.address + offset, &value)?;
            offset += MAX_VALUE_SIZE as u64;
        }

        Ok(())
    }
}

#[derive(Debug, PartialEq)]
struct InternalNode {
    address: Ptr,
    keys: Vec<Key>,
    values: Vec<Value>,
    children: Vec<Ptr>, // Pointers to the children + the key
}

impl InternalNode {
    fn is_full(&self) -> bool {
        self.keys.len() >= CAPACITY as usize
    }

    // Returns the index of the child where the given `key` belongs.
    fn get_child_address(&self, key: &Key) -> Ptr {
        assert!(!self.children.is_empty());

        let idx = self.keys.binary_search(key).unwrap_or_else(|x| x);

        self.children[idx]
    }

    fn save(&self, memory: &impl Memory64) -> Result<(), WriteError> {
        println!("saving node at address {:?}", self.address);
        let header = NodeHeader {
            node_type: INTERNAL_NODE_TYPE,
            num_entries: self.keys.len() as u64,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<NodeHeader>(),
            )
        };

        let header_len = core::mem::size_of::<NodeHeader>() as u64;

        write(memory, self.address, header_slice)?;

        let mut offset = header_len;

        assert_eq!(self.keys.len(), self.values.len());
        assert_eq!(self.children.len(), self.keys.len() + 1);
        // Write the entries.
        for (key, value) in self.keys.iter().zip(self.values.iter()) {
            // Write the size of the key.
            write(
                memory,
                self.address + offset,
                &(key.len() as u32).to_le_bytes(),
            )?;
            offset += 4;
            write(memory, self.address + offset, &key)?;
            offset += MAX_KEY_SIZE as u64;
            write(
                memory,
                self.address + offset,
                &(value.len() as u32).to_le_bytes(),
            )?;
            offset += 4;
            write(memory, self.address + offset, &value)?;
            offset += MAX_VALUE_SIZE as u64;
        }

        // Write the children
        for child in self.children.iter() {
            write(memory, self.address + offset, &child.to_le_bytes())?;
            offset += 8;
        }

        Ok(())
    }
}

#[derive(Debug, PartialEq)]
enum Node {
    Internal(InternalNode),
    Leaf(LeafNode),
}

#[repr(packed)]
#[derive(Debug, PartialEq)]
struct NodeHeader {
    // 1 if internal node, 0 if a leaf node.
    node_type: u8, // TODO: can be one bit.
    //flags: u8 // a byte for flags (e.g. node type, is root, etc.)
    num_entries: u64, // TODO: this can be smaller than u64,
}

impl Node {
    fn new_leaf(address: u64) -> Self {
        Self::Leaf(LeafNode {
            address,
            keys: vec![],
            values: vec![],
        })
    }

    fn new_internal(address: u64) -> InternalNode {
        InternalNode {
            address,
            keys: vec![],
            values: vec![],
            children: vec![],
        }
    }

    fn load(address: u64, memory: &impl Memory64) -> Node {
        let mut header: NodeHeader = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<NodeHeader>(),
            )
        };
        let header_len = core::mem::size_of::<NodeHeader>() as u64;
        /*if memory.size() == 0 {
            return Err(LoadError::MemoryEmpty);
        }*/
        memory.read(address, header_slice);

        println!("num_entries: {:?}", header.num_entries);

        if header.node_type == LEAF_NODE_TYPE {
            // Load the entries.
            let mut keys = vec![];
            let mut values = vec![];
            let mut offset = header_len;
            for _ in 0..header.num_entries {
                println!("reading entry");
                let key_size = read_u32(memory, address + offset);
                println!("key size: {:?}", key_size);
                offset += 4;
                let mut key = vec![0; key_size as usize];
                memory.read(address + offset, &mut key);
                println!("key: {:?}", key);
                offset += MAX_KEY_SIZE as u64;

                let value_size = read_u32(memory, address + offset);
                offset += 4;
                let mut value = vec![0; value_size as usize];
                memory.read(address + offset, &mut value);
                offset += MAX_VALUE_SIZE as u64;

                keys.push(key);
                values.push(value);
            }
            Node::Leaf(LeafNode {
                address,
                keys,
                values,
            })
        } else {
            let mut keys = vec![];
            let mut children = vec![];
            let mut values = vec![];
            let mut offset = header_len;
            for _ in 0..header.num_entries {
                println!("reading entry");
                let key_size = read_u32(memory, address + offset);
                println!("key size: {:?}", key_size);
                offset += 4;
                let mut key = vec![0; key_size as usize];
                memory.read(address + offset, &mut key);
                println!("key: {:?}", key);
                offset += MAX_KEY_SIZE as u64;

                let value_size = read_u32(memory, address + offset);
                offset += 4;
                let mut value = vec![0; value_size as usize];
                memory.read(address + offset, &mut value);
                offset += MAX_VALUE_SIZE as u64;

                keys.push(key);
                values.push(value);
            }

            // Load children
            for _ in 0..header.num_entries + 1 {
                println!("reading child");
                let child = read_u64(memory, address + offset);
                offset += 8;
                children.push(child);
            }

            Node::Internal(InternalNode {
                address,
                values,
                keys,
                children,
            })
        }
    }

    fn is_full(&self) -> bool {
        match &self {
            Self::Leaf(leaf) => leaf.is_full(),
            Self::Internal(internal) => internal.is_full(),
        }
    }

    fn save(&self, memory: &impl Memory64) -> Result<(), WriteError> {
        match &self {
            Self::Leaf(leaf) => leaf.save(memory),
            Self::Internal(internal) => internal.save(memory),
        }
    }
}

pub struct Range;

impl<M: Memory64> StableBTreeMap<M> {
    // TODO: make branching factor configurable.
    pub fn new(memory: M, max_key_size: u32, max_value_size: u32) -> Self {
        let header_len = core::mem::size_of::<Header>() as u64;

        let header = Header {
            magic: *b"BTR",
            version: LAYOUT_VERSION,
            root_offset: NULL,
            free_list: header_len,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<Header>(),
            )
        };

        if memory.size() == 0 {
            if memory.grow(1) == -1 {
                panic!("OOM");
                //return Err(AllocError::GrowFailed {
                //   current: 0,
                //   delta: 1,
                //});
            }
        }

        memory.write(0, header_slice);

        Self {
            memory,
            root_offset: header.root_offset,
            free_list: header.free_list,
            /*max_key_size,
            max_value_size,
            root: Node::Leaf(LeafNode {
                keys: vec![],
                values: vec![],
            }),*/
        }
    }

    pub fn load(memory: M) -> Result<Self, LoadError> {
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
        memory.read(0, header_slice);
        if &header.magic != b"BTR" {
            return Err(LoadError::BadMagic(header.magic));
        }
        if header.version != LAYOUT_VERSION {
            return Err(LoadError::UnsupportedVersion(header.version));
        }
        Ok(Self {
            memory,
            root_offset: header.root_offset,
            free_list: header.free_list,
            /*max_key_size: 0,
            max_value_size: 0,
            root: Node::Leaf(LeafNode {
                keys: vec![],
                values: vec![],
            }),*/
        })
    }

    pub fn insert(&mut self, key: Key, value: Value) -> Option<Value> {
        let root = if self.root_offset == NULL {
            // Allocate a node.
            let node_header_len = core::mem::size_of::<NodeHeader>() as u64;
            let node_size = node_header_len + CAPACITY * ((MAX_KEY_SIZE + MAX_VALUE_SIZE) as u64);

            // TODO: check there's still enough space.
            // TODO: save updated free list to memory.
            let node_address = self.free_list;

            self.free_list += node_size;
            self.root_offset = node_address;

            Node::new_leaf(node_address)
        } else {
            Node::load(self.root_offset, &self.memory)
        };

        // if node is not full
        if !root.is_full() {
            self.insert_nonfull(root, key, value)
        } else {
            // The root is full. Allocate a new node that will be used as the new root.
            let mut new_root = self.allocate_internal_node();
            new_root.children.push(self.root_offset);
            println!(
                "Updating root from {:?} to {:?}",
                self.root_offset, new_root.address
            );
            self.root_offset = new_root.address;

            new_root.save(&self.memory).unwrap();

            self.split_child(&mut new_root, 0);
            self.insert_nonfull(Node::Internal(new_root), key, value)
        }
    }

    pub fn get(&self, key: &Key) -> Option<Value> {
        if self.root_offset == NULL {
            return None;
        }

        Self::get_helper(self.root_offset, key, &self.memory)
    }

    fn get_helper(node_addr: Ptr, key: &Key, memory: &impl Memory64) -> Option<Value> {
        let node = Node::load(node_addr, memory);
        match node {
            Node::Leaf(LeafNode { keys, values, .. }) => {
                println!("Leaf node");
                println!("keys: {:?}", keys);

                match keys.binary_search(key) {
                    Ok(idx) => Some(values[idx].clone()),
                    _ => None, // Key not found.
                }
            }
            Node::Internal(internal) => {
                println!("Internal node: {:?}", internal);
                match internal.keys.binary_search(key) {
                    Ok(idx) => Some(internal.values[idx].clone()),
                    Err(idx) => {
                        // The key isn't in the node. Look for the node in the child.
                        let child_address = internal.children[idx];
                        println!("Child address: {:?}", child_address);

                        // Recurse
                        Self::get_helper(child_address, key, memory)
                    }
                }
            }
        }
    }

    /*
    pub fn remove(&mut self, key: &[u8]) -> Option<&[u8]> {
        todo!();
    }

    pub fn range<T, R>(&self, range: R) -> Range
    where
        R: RangeBounds<T>,
    {
        todo!();
    }*/

    fn allocate_leaf_node(&mut self) -> LeafNode {
        let node_header_len = core::mem::size_of::<NodeHeader>() as u64;
        let node_size = node_header_len + CAPACITY * ((MAX_KEY_SIZE + MAX_VALUE_SIZE) as u64);

        // TODO: check there's still enough space.
        // TODO: save updated free list to memory.
        let node_address = self.free_list;

        self.free_list += node_size;
        LeafNode::new(node_address)
    }

    fn allocate_internal_node(&mut self) -> InternalNode {
        let node_header_len = core::mem::size_of::<NodeHeader>() as u64;
        let node_size = node_header_len + CAPACITY * ((MAX_KEY_SIZE + MAX_VALUE_SIZE) as u64) + /* children pointers */ 8 * (CAPACITY + 1);

        // TODO: check there's still enough space.
        // TODO: save updated free list to memory.
        let node_address = self.free_list;

        self.free_list += node_size;

        Node::new_internal(node_address)
    }

    fn split_child(&mut self, parent: &mut InternalNode, full_child_idx: usize) {
        println!("SPLIT CHILD");
        assert!(!parent.is_full());
        let full_child = Node::load(parent.children[full_child_idx], &self.memory);

        // The child must be already full.
        assert!(full_child.is_full());

        // Create a sibling to this full child.
        match full_child {
            Node::Leaf(mut full_child_leaf) => {
                let mut sibling = self.allocate_leaf_node();

                // Move the values above the median into the new sibling.
                let mut keys_to_move = full_child_leaf.keys.split_off(B as usize - 1);
                let mut values_to_move = full_child_leaf.values.split_off(B as usize - 1);

                let median_key = keys_to_move.remove(0);
                let median_value = values_to_move.remove(0);

                println!("sibling keys: {:?}", keys_to_move);
                sibling.keys = keys_to_move;
                sibling.values = values_to_move;

                // Add sibling as a new child in parent.
                parent.children.insert(full_child_idx + 1, sibling.address);
                parent.keys.insert(full_child_idx, median_key);
                parent.values.insert(full_child_idx, median_value);

                println!("parent keys: {:?}", parent.keys);
                println!("child keys: {:?}", full_child_leaf.keys);

                full_child_leaf.save(&self.memory);
                sibling.save(&self.memory);
                parent.save(&self.memory);
            }
            Node::Internal(_) => todo!(), //self.allocate_internal_node();
        };
    }

    fn insert_nonfull(&mut self, mut node: Node, key: Key, value: Value) -> Option<Value> {
        println!("INSERT NONFULL");
        match node {
            Node::Leaf(LeafNode {
                ref mut keys,
                ref mut values,
                ..
            }) => {
                let ret = match keys.binary_search(&key) {
                    Ok(idx) => {
                        // The key was already in the map. Overwrite and return the previous value.
                        let old_value = values[idx].clone(); // TODO: remove this clone?
                        values[idx] = value;
                        Some(old_value)
                    }
                    Err(idx) => {
                        // Key not present.
                        keys.insert(idx, key);
                        values.insert(idx, value);
                        None
                    }
                };

                node.save(&self.memory).unwrap();
                ret
            }
            Node::Internal(ref mut internal) => {
                // Find the child that we should add to.
                // Load the child from memory.
                //
                // if child is full, split the child
                // insert_nonfull(child_after_split, key, value,
                println!("internal node: {:?}", internal);

                let idx = internal.keys.binary_search(&key).unwrap_or_else(|x| x);
                let child_offset = internal.children[idx];
                println!("loading child at offset: {}", child_offset);
                let child = Node::load(child_offset, &self.memory);

                println!("Child Node: {:?}", child);

                if child.is_full() {
                    println!("SPLIT CHILD FROM INSERT NONFULL");
                    self.split_child(internal, idx);
                }

                self.insert_nonfull(child, key, value)
            }
        }

        //todo!();
        /*match node {
            Node::Leaf(LeafNode { entries }) => {
                match entries.binary_search_by_key(&key, |(key, value)| key.to_vec()) {
                    // TODO: get rid of to_vec
                    Ok(idx) => {
                        // The key was already in the map. Overwrite and return the previous value.
                        let old_value = entries[idx].1.clone();
                        entries[idx].1 = value;
                        Some(old_value)
                    }
                    Err(idx) => {
                        // Key not present.
                        entries.insert(idx, (key, value));
                        None
                    }
                }
            }
            Node::Internal => todo!(),
        }*/
    }
}

/// A helper function that reads a single 32bit integer encoded as
/// little-endian from the specified memory at the specified offset.
fn read_u32<M: Memory64>(m: &M, offset: u64) -> u32 {
    let mut buf: [u8; 4] = [0; 4];
    m.read(offset, &mut buf);
    u32::from_le_bytes(buf)
}

/// A helper function that reads a single 32bit integer encoded as
/// little-endian from the specified memory at the specified offset.
fn read_u64<M: Memory64>(m: &M, offset: u64) -> u64 {
    let mut buf: [u8; 8] = [0; 8];
    m.read(offset, &mut buf);
    u64::from_le_bytes(buf)
}

fn write(memory: &impl Memory64, offset: u64, bytes: &[u8]) -> Result<(), WriteError> {
    let last_byte = offset
        .checked_add(bytes.len() as u64)
        .ok_or(WriteError::AddressSpaceOverflow)?;
    let size_pages = memory.size();
    let size_bytes = size_pages
        .checked_mul(WASM_PAGE_SIZE)
        .ok_or(WriteError::AddressSpaceOverflow)?;
    if size_bytes < last_byte {
        let diff_bytes = last_byte - size_bytes;
        let diff_pages = diff_bytes
            .checked_add(WASM_PAGE_SIZE - 1)
            .ok_or(WriteError::AddressSpaceOverflow)?
            / WASM_PAGE_SIZE;
        if memory.grow(diff_pages) == -1 {
            return Err(WriteError::GrowFailed {
                current: size_pages,
                delta: diff_pages,
            });
        }
    }
    memory.write(offset, bytes);
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Memory64;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn node_save_load_is_noop() {
        let mem = make_memory();
        let mut node = Node::new_leaf(0);

        // TODO: can we get rid of this if let?
        if let Node::Leaf(ref mut leaf) = node {
            leaf.keys.push(vec![1, 2, 3]);
            leaf.values.push(vec![4, 5, 6]);
        }

        node.save(&mem).unwrap();

        let node_2 = Node::load(0, &mem);

        assert_eq!(node, node_2);
    }

    #[test]
    fn insert_get() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 0, 0);

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), None);
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![4, 5, 6]));
    }

    #[test]
    fn insert_overwrites_previous_value() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 0, 0);

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), None);
        assert_eq!(
            btree.insert(vec![1, 2, 3], vec![7, 8, 9]),
            Some(vec![4, 5, 6])
        );
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![7, 8, 9]));
    }

    #[test]
    fn insert_get_multiple() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 0, 0);

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), None);
        assert_eq!(btree.insert(vec![4, 5], vec![7, 8, 9, 10]), None);
        assert_eq!(btree.insert(vec![], vec![11]), None);
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![4, 5, 6]));
        assert_eq!(btree.get(&vec![4, 5]), Some(vec![7, 8, 9, 10]));
        assert_eq!(btree.get(&vec![]), Some(vec![11]));
    }

    #[test]
    fn insert_same_key_multiple() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 0, 0);

        assert_eq!(btree.insert(vec![1], vec![2]), None);

        for i in 2..100 {
            assert_eq!(btree.insert(vec![1], vec![i + 1]), Some(vec![i]));
        }
    }

    #[test]
    fn insert_more_than_b() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 0, 0);

        assert_eq!(btree.insert(vec![1], vec![2]), None);
        assert_eq!(btree.insert(vec![2], vec![2]), None);
        assert_eq!(btree.insert(vec![3], vec![2]), None);
        assert_eq!(btree.insert(vec![4], vec![2]), None);
        assert_eq!(btree.insert(vec![5], vec![2]), None);
        assert_eq!(btree.insert(vec![6], vec![2]), None);
        assert_eq!(btree.insert(vec![7], vec![2]), None);
        assert_eq!(btree.insert(vec![8], vec![2]), None);
        assert_eq!(btree.insert(vec![9], vec![2]), None);
        assert_eq!(btree.insert(vec![10], vec![2]), None);
        assert_eq!(btree.insert(vec![11], vec![2]), None);
        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![2]), None);

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..13 {
            println!("i: {:?}", i);
            assert_eq!(btree.get(&vec![i]), Some(vec![2]));
        }
    }
}

#[cfg(test)]
mod test_internal_node {
    use super::*;
    use crate::Memory64;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn get_child_address_1() {
        //        [1]
        //  (10) /   \ (4)
        let node = InternalNode {
            address: 0,
            keys: vec![vec![1]],
            values: vec![vec![]],
            children: vec![10, 4],
        };

        assert_eq!(node.get_child_address(&vec![2]), 4);
        assert_eq!(node.get_child_address(&vec![0]), 10);
        assert_eq!(node.get_child_address(&vec![1]), 10); // The value of the key in the internal node is in the left child.
    }

    #[test]
    fn get_child_address_2() {
        //        [1]
        //  (10) /   \ (4)
        let node = InternalNode {
            address: 0,
            keys: vec![vec![], vec![1], vec![1, 2]],
            values: vec![vec![], vec![], vec![]],
            children: vec![1, 2, 3, 4],
        };

        assert_eq!(node.get_child_address(&vec![]), 1);
        assert_eq!(node.get_child_address(&vec![0]), 2);
        assert_eq!(node.get_child_address(&vec![1, 2]), 3);
        assert_eq!(node.get_child_address(&vec![1, 2, 3]), 4);
    }
}
