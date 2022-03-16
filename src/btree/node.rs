use crate::btree::{read_u32, read_u64, write, WriteError};
use crate::Memory64;
use core::mem;

// Taken from `BTreeMap`.
const B: u32 = 6;
const CAPACITY: u32 = 2 * B - 1;

const LEAF_NODE_TYPE: u8 = 0;
const INTERNAL_NODE_TYPE: u8 = 1;

type Ptr = u64;
type Key = Vec<u8>;
type Value = Vec<u8>;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum NodeType {
    Leaf,
    Internal,
}

#[derive(Debug, PartialEq)]
pub struct Node {
    pub address: Ptr,
    pub entries: Vec<(Key, Value)>,
    pub children: Vec<Ptr>,
    pub node_type: NodeType,
    pub max_key_size: u32,
    pub max_value_size: u32,
}

impl Node {
    pub fn get_max(&self, memory: &impl Memory64) -> (Key, Value) {
        if self.children.is_empty() {
            self.entries.last().unwrap().clone()
        } else {
            let last_child = Self::load(
                *self.children.last().unwrap(),
                memory,
                self.max_key_size,
                self.max_value_size,
            );
            last_child.get_max(memory)
        }
    }

    pub fn get_min(&self, memory: &impl Memory64) -> (Key, Value) {
        if self.children.is_empty() {
            self.entries[0].clone()
        } else {
            let first_child = Self::load(
                self.children[0],
                memory,
                self.max_key_size,
                self.max_value_size,
            );
            first_child.get_min(memory)
        }
    }

    pub fn is_full(&self) -> bool {
        self.entries.len() >= CAPACITY as usize
    }

    /// Swaps the entry at index `idx` with the given entry, returning the old entry.
    pub fn swap_entry(&mut self, idx: usize, mut entry: (Key, Value)) -> (Key, Value) {
        mem::swap(&mut self.entries[idx], &mut entry);
        entry
    }

    pub fn save(&self, memory: &impl Memory64) -> Result<(), WriteError> {
        match self.node_type {
            NodeType::Leaf => {
                assert!(self.children.is_empty());
            }
            NodeType::Internal => {
                assert_eq!(self.children.len(), self.entries.len() + 1);
            }
        };

        //assert!(!self.keys.is_empty()); TODO: enable this assertion

        // INVARIANT: the children's keys.
        /*for i in 0..self.keys.len() {
            let left_child = Node::load(self.children[i], memory);
            let right_child = Node::load(self.children[i + 1], memory);

            assert!(
                left_child.keys().last().unwrap().clone() < self.keys[i],
                "Keys not aligned. Left child: {:?}\nParent: {:?}",
                left_child,
                self
            );
            assert!(right_child.keys()[0] > self.keys[i]);
        }*/

        let header = NodeHeader {
            node_type: match self.node_type {
                NodeType::Leaf => LEAF_NODE_TYPE,
                NodeType::Internal => INTERNAL_NODE_TYPE,
            },
            num_entries: self.entries.len() as u64,
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
        for (key, value) in self.entries.iter() {
            // Write the size of the key.
            write(
                memory,
                self.address + offset,
                &(key.len() as u32).to_le_bytes(),
            )?;
            offset += 4;
            write(memory, self.address + offset, &key)?;
            offset += self.max_key_size as u64;
            write(
                memory,
                self.address + offset,
                &(value.len() as u32).to_le_bytes(),
            )?;
            offset += 4;
            write(memory, self.address + offset, &value)?;
            offset += self.max_value_size as u64;
        }

        // Write the children
        for child in self.children.iter() {
            write(memory, self.address + offset, &child.to_le_bytes())?;
            offset += 8;
        }

        Ok(())
    }

    pub fn load(
        address: Ptr,
        memory: &impl Memory64,
        max_key_size: u32,
        max_value_size: u32,
    ) -> Self {
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
        //println!("reading");
        memory.read(address, header_slice);
        //println!("Header: {:?}", header);

        //println!("num_entries: {:?}", header.num_entries);
        // Load the entries.
        let mut entries = vec![];
        let mut offset = header_len;
        for _ in 0..header.num_entries {
            let key_size = read_u32(memory, address + offset);
            offset += 4;
            let mut key = vec![0; key_size as usize];
            memory.read(address + offset, &mut key);
            offset += max_key_size as u64;

            let value_size = read_u32(memory, address + offset);
            offset += 4;
            let mut value = vec![0; value_size as usize];
            memory.read(address + offset, &mut value);
            offset += max_value_size as u64;

            entries.push((key, value));
        }

        let mut children = vec![];
        if header.node_type == INTERNAL_NODE_TYPE {
            // Load children
            for _ in 0..header.num_entries + 1 {
                let child = read_u64(memory, address + offset);
                offset += 8;
                children.push(child);
            }

            assert_eq!(children.len(), entries.len() + 1);
            /*// NOTE: this can slow things down.
            for i in 0..keys.len() {
                let left_child = Node::load(children[i], memory);
                let right_child = Node::load(children[i + 1], memory);

                assert!(left_child.keys().last().unwrap().clone() < keys[i]);
                assert!(right_child.keys()[0] > keys[i]);
            }*/
        }

        Self {
            address,
            entries,
            children,
            node_type: match header.node_type {
                LEAF_NODE_TYPE => NodeType::Leaf,
                INTERNAL_NODE_TYPE => NodeType::Internal,
                other => unreachable!("Unknown node type {}", other),
            },
            max_key_size,
            max_value_size,
        }
    }
}

#[repr(packed)]
struct NodeHeader {
    // TODO: add magic
    node_type: u8,
    num_entries: u64,
}

/// Returns the size of a node in bytes.
///
/// The following is the layout of a node in memory:
///
///  1) Node Header
/// 
///  2) Each node can contain up to `CAPACITY` entries, each entry contains:
///     - size of key (4 bytes)
///     - key (`max_key_size` bytes)
///     - size of value (4 bytes)
///     - value (`max_value_size` bytes)
/// 
///  3) Each node can contain up to `CAPACITY + 1` children, each child contains:
///     - child (8 bytes)
pub fn get_node_size_in_bytes(max_key_size: u32, max_value_size: u32) -> u32 {
    let node_header_len = core::mem::size_of::<NodeHeader>() as u32;
    let entry_size = max_key_size + 4 + max_value_size + 4;
    let child_size = core::mem::size_of::<Ptr>() as u32;

    node_header_len + CAPACITY * entry_size + (CAPACITY + 1) * child_size
}

#[cfg(test)]
mod test {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn node_save_load_is_noop() {
        let mem = make_memory();
        let mut node = Node {
            address: 0,
            entries: vec![(vec![1, 2, 3], vec![4, 5, 6])],
            children: vec![1, 2],
            node_type: NodeType::Internal,
            max_key_size: 3,
            max_value_size: 3,
        };

        node.save(&mem).unwrap();

        let node_2 = Node::load(0, &mem, 3, 3);

        assert_eq!(node, node_2);
    }
}
