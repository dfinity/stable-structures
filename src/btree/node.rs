use crate::btree::{allocator::Allocator, write, read_u64, read_u32, WriteError};
use crate::{Memory64, WASM_PAGE_SIZE};

const LAYOUT_VERSION: u8 = 1;
const NULL: u64 = 0;

const MAX_KEY_SIZE: u32 = 64;
const MAX_VALUE_SIZE: u32 = 64;

// Taken from `BTreeMap`.
const B: u64 = 6; // The minimum degree.
const CAPACITY: u64 = 2 * B - 1;

const LEAF_NODE_TYPE: u8 = 0;
const INTERNAL_NODE_TYPE: u8 = 1;

type Ptr = u64;

type Key = Vec<u8>;
type Value = Vec<u8>;

#[derive(Debug, PartialEq)]
pub struct LeafNode {
    pub address: Ptr,
    pub keys: Vec<Key>,
    pub values: Vec<Value>,
}

impl LeafNode {
    pub fn new(address: u64) -> Self {
        LeafNode {
            address,
            keys: vec![],
            values: vec![],
        }
    }

    pub fn is_full(&self) -> bool {
        self.keys.len() >= CAPACITY as usize
    }

    pub fn save(&self, memory: &impl Memory64) -> Result<(), WriteError> {
        println!("saving node at address {:?}", self.address);
        let header = NodeHeader {
            node_type: LEAF_NODE_TYPE,
            num_entries: self.values.len() as u64,
        };

        println!("header: {:?}", header);

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
pub struct InternalNode {
    pub address: Ptr,
    pub keys: Vec<Key>,
    pub values: Vec<Value>,
    pub children: Vec<Ptr>, // Pointers to the children + the key
}

impl InternalNode {
    pub fn is_full(&self) -> bool {
        self.keys.len() >= CAPACITY as usize
    }

    // Returns the index of the child where the given `key` belongs.
    fn get_child_address(&self, key: &Key) -> Ptr {
        assert!(!self.children.is_empty());

        let idx = self.keys.binary_search(key).unwrap_or_else(|x| x);

        self.children[idx]
    }

    pub fn save(&self, memory: &impl Memory64) -> Result<(), WriteError> {
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
pub enum Node {
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
    pub fn new_leaf(address: u64) -> Self {
        Self::Leaf(LeafNode {
            address,
            keys: vec![],
            values: vec![],
        })
    }

    pub fn new_internal(address: u64) -> InternalNode {
        InternalNode {
            address,
            keys: vec![],
            values: vec![],
            children: vec![],
        }
    }

    pub fn load(address: u64, memory: &impl Memory64) -> Node {
        println!("Loading node at address: {}", address);
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
        println!("reading");
        memory.read(address, header_slice);
        println!("Header: {:?}", header);

        //println!("num_entries: {:?}", header.num_entries);

        if header.node_type == LEAF_NODE_TYPE {
            // Load the entries.
            let mut keys = vec![];
            let mut values = vec![];
            let mut offset = header_len;
            for _ in 0..header.num_entries {
                //println!("reading entry");
                let key_size = read_u32(memory, address + offset);
                //println!("key size: {:?}", key_size);
                offset += 4;
                let mut key = vec![0; key_size as usize];
                memory.read(address + offset, &mut key);
                //println!("key: {:?}", key);
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
        } else if header.node_type == INTERNAL_NODE_TYPE {
            let mut keys = vec![];
            let mut children = vec![];
            let mut values = vec![];
            let mut offset = header_len;
            //println!("num entries: {}", header.num_entries);
            for _ in 0..header.num_entries {
                //println!("reading entry");
                let key_size = read_u32(memory, address + offset);
                //println!("key size: {:?}", key_size);
                offset += 4;
                let mut key = vec![0; key_size as usize];
                memory.read(address + offset, &mut key);
                //println!("key: {:?}", key);
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
        } else {
            unreachable!("Unknown node type");
        }
    }

    pub fn is_full(&self) -> bool {
        match &self {
            Self::Leaf(leaf) => leaf.is_full(),
            Self::Internal(internal) => internal.is_full(),
        }
    }

    pub fn address(&self) -> Ptr {
        match &self {
            Self::Leaf(leaf) => leaf.address,
            Self::Internal(internal) => internal.address,
        }
    }

    pub fn keys(&self) -> &[Key] {
        match &self {
            Self::Leaf(leaf) => &leaf.keys,
            Self::Internal(internal) => &internal.keys,
        }
    }

    pub fn keys_mut(&mut self) -> &mut Vec<Key> {
        match self {
            Self::Leaf(leaf) => &mut leaf.keys,
            Self::Internal(internal) => &mut internal.keys,
        }
    }

    pub fn values(&self) -> &[Value] {
        match &self {
            Self::Leaf(leaf) => &leaf.values,
            Self::Internal(internal) => &internal.values,
        }
    }

    pub fn values_mut(&mut self) -> &mut Vec<Value> {
        match self {
            Self::Leaf(leaf) => &mut leaf.values,
            Self::Internal(internal) => &mut internal.values,
        }
    }

    pub fn save(&self, memory: &impl Memory64) -> Result<(), WriteError> {
        match &self {
            Self::Leaf(leaf) => leaf.save(memory),
            Self::Internal(internal) => internal.save(memory),
        }
    }
}

// TODO: This function isn't used.
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
