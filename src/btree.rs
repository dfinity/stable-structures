use crate::{Memory64, WASM_PAGE_SIZE};
mod allocator;
mod node;
use crate::btree::allocator::Allocator;
use crate::btree::node::{Node, NodeType};

const LAYOUT_VERSION: u8 = 1;
const NULL: u64 = 0;

// Taken from `BTreeMap`.
const B: u64 = 6; // The minimum degree.
const CAPACITY: u64 = 2 * B - 1;

type Ptr = u64;

#[repr(packed)]
struct BTreeHeader {
    magic: [u8; 3],
    version: u8,
    root_offset: u64,
    max_key_size: u32,
    max_value_size: u32,
}

#[derive(Debug)]
pub enum LoadError {
    MemoryEmpty,
    BadMagic([u8; 3]),
    UnsupportedVersion(u8),
}

#[derive(Debug, PartialEq, Eq)]
pub enum WriteError {
    GrowFailed { current: u64, delta: u64 },
    AddressSpaceOverflow,
}

// TODO: fix node allocation size.
// TODO: look into how we can avoid unreachables and unwraps.
// TODO: review code and update documentation.

/// A "stable" map based on a B-tree.
///
/// OPEN QUESTIONS:
///
/// 1) Currently the branching factor `B` is hard-coded constant. That's what Rust's `BTreeMap`
///    uses. We can either make this a configurable parameter, or dynamically infer it from
///    the sizes of the keys/values (e.g. choose a branching factor that makes a node fit a whole
///    OS page.
///
/// 2) Right now the memory allocator is very simple and, if we're not being careful, it can lead
///    to bugs (e.g. deallocating twice). Should we try to add more stringent checks, or is this
///    goog enough?
///
/// 3) Crashing vs returning an error.
pub struct StableBTreeMap<M: Memory64 + Clone> {
    root_offset: Ptr,
    // The maximum size a key can have.
    max_key_size: u32,

    // The maximum size a value can have.
    max_value_size: u32,

    allocator: Allocator<M>,
    memory: M,
}

type Key = Vec<u8>;
type Value = Vec<u8>;

impl<M: Memory64 + Clone> StableBTreeMap<M> {
    // TODO: make branching factor configurable.
    pub fn new(memory: M, max_key_size: u32, max_value_size: u32) -> Result<Self, WriteError> {
        let header_len = core::mem::size_of::<BTreeHeader>() as u64;

        let btree = Self {
            memory: memory.clone(),
            root_offset: NULL,
            allocator: Allocator::new(memory, header_len, 4096 /* TODO */)?,
            max_key_size,
            max_value_size,
        };

        btree.save()?;
        Ok(btree)
    }

    /// Loads the map from memory.
    pub fn load(memory: M) -> Result<Self, LoadError> {
        let mut header: BTreeHeader = unsafe { core::mem::zeroed() };
        let header_slice = unsafe {
            core::slice::from_raw_parts_mut(
                &mut header as *mut _ as *mut u8,
                core::mem::size_of::<BTreeHeader>(),
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

        let header_len = core::mem::size_of::<BTreeHeader>() as u64;

        Ok(Self {
            memory: memory.clone(),
            root_offset: header.root_offset,
            allocator: Allocator::load(memory, header_len)?,
            max_key_size: header.max_key_size,
            max_value_size: header.max_value_size,
        })
    }

    fn save(&self) -> Result<(), WriteError> {
        let header = BTreeHeader {
            magic: *b"BTR",
            version: LAYOUT_VERSION,
            root_offset: self.root_offset,
            max_key_size: self.max_key_size,
            max_value_size: self.max_value_size,
        };

        let header_slice = unsafe {
            core::slice::from_raw_parts(
                &header as *const _ as *const u8,
                core::mem::size_of::<BTreeHeader>(),
            )
        };

        write(&self.memory, 0, header_slice)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// The previous value of the key, if present, is returned.
    pub fn insert(&mut self, key: Key, value: Value) -> Result<Option<Value>, InsertError> {
        if key.len() > self.max_key_size as usize {
            return Err(InsertError::KeyTooLarge {
                given: key.len(),
                max: self.max_key_size as usize,
            });
        }

        if value.len() > self.max_value_size as usize {
            return Err(InsertError::ValueTooLarge {
                given: key.len(),
                max: self.max_value_size as usize,
            });
        }

        let root = if self.root_offset == NULL {
            let node = self.allocate_node(NodeType::Leaf);
            self.root_offset = node.address;
            node
        } else {
            self.load_node(self.root_offset)
        };

        if !root.is_full() {
            Ok(self.insert_nonfull(root, key, value)?)
        } else {
            // The root is full. Allocate a new node that will be used as the new root.
            let mut new_root = self.allocate_node(NodeType::Internal);
            new_root.children.push(self.root_offset);
            self.root_offset = new_root.address;

            new_root.save(&self.memory).unwrap();

            self.split_child(&mut new_root, 0)?;
            Ok(self.insert_nonfull(new_root, key, value)?)
        }
    }

    fn insert_nonfull(
        &mut self,
        mut node: Node,
        key: Key,
        value: Value,
    ) -> Result<Option<Value>, WriteError> {
        println!("INSERT NONFULL: key {:?}", key);
        match node.node_type {
            NodeType::Leaf => {
                let ret = match node.entries.binary_search_by(|e| e.0.cmp(&key)) {
                    Ok(idx) => {
                        // The key was already in the map. Overwrite and return the previous value.
                        let (_, old_value) = node.swap_entry(idx, (key, value));
                        Some(old_value)
                    }
                    Err(idx) => {
                        // Key not present.
                        node.entries.insert(idx, (key, value));
                        None
                    }
                };

                node.save(&self.memory)?;
                self.save()?; // TODO: is this necessary?
                Ok(ret)
            }
            NodeType::Internal => {
                // Find the child that we should add to.
                let idx = node
                    .entries
                    .binary_search_by(|e| e.0.cmp(&key))
                    .unwrap_or_else(|idx| idx);

                let child = self.load_node(node.children[idx]);
                if child.is_full() {
                    self.split_child(&mut node, idx)?;
                }

                let idx = node
                    .entries
                    .binary_search_by(|e| e.0.cmp(&key))
                    .unwrap_or_else(|idx| idx);
                let child = self.load_node(node.children[idx]);

                debug_assert!(!child.is_full());

                self.insert_nonfull(child, key, value)
            }
        }
    }

    /// Returns the value associated with the given key if it exists.
    pub fn get(&self, key: &Key) -> Option<Value> {
        if self.root_offset == NULL {
            return None;
        }

        self.get_helper(self.root_offset, key)
    }

    fn get_helper(&self, node_addr: Ptr, key: &Key) -> Option<Value> {
        let node = self.load_node(node_addr);
        match node.entries.binary_search_by(|e| e.0.cmp(&key)) {
            Ok(idx) => Some(node.entries[idx].1.clone()),
            Err(idx) => {
                match node.node_type {
                    NodeType::Leaf => None, // Key not found.
                    NodeType::Internal => {
                        // The key isn't in the node. Look for the key in the child.
                        self.get_helper(node.children[idx], key)
                    }
                }
            }
        }
    }

    /// Removes a key from the map, returning the previous value at the key if it exists.
    pub fn remove(&mut self, key: &Key) -> Result<Option<Value>, WriteError> {
        if self.root_offset == NULL {
            return Ok(None);
        }

        let ret = self.remove_helper(self.root_offset, key);
        self.save()?;
        ret
    }

    // A helper method for recursively removing a key from the B-tree.
    fn remove_helper(&mut self, node_addr: Ptr, key: &Key) -> Result<Option<Value>, WriteError> {
        println!("REMOVING KEY: {:?}", key);
        let mut node = self.load_node(node_addr);

        if node.address != self.root_offset {
            debug_assert!(node.entries.len() >= B as usize);
        }

        match node.node_type {
            NodeType::Leaf => {
                match node.entries.binary_search_by(|e| e.0.cmp(&key)) {
                    Ok(idx) => {
                        // Case 1: The node is a leaf node and the key exists in it.
                        // This is the simplest case. The key is removed from the leaf.
                        let value = node.entries.remove(idx).1;
                        node.save(&self.memory)?;

                        if node.entries.is_empty() {
                            debug_assert_eq!(
                                node.address, self.root_offset,
                                "Removal can only result in an empty leaf node if that node is the root"
                            );

                            if node.address == self.root_offset {
                                self.allocator.deallocate(node.address);
                                self.root_offset = NULL;
                            }
                        }

                        Ok(Some(value))
                    }
                    _ => Ok(None), // Key not found.
                }
            }
            NodeType::Internal => {
                match node.entries.binary_search_by(|e| e.0.cmp(&key)) {
                    Ok(idx) => {
                        // Case 2: The node is an internal node and the key exists in it.

                        let value = node.entries[idx].1.clone(); // TODO: no clone

                        // Check if the child that precedes `key` has at least `B` keys.
                        let left_child = self.load_node(node.children[idx]);
                        if left_child.entries.len() >= B as usize {
                            // Case 2.a: The node's left child has >= `B` keys.
                            //
                            //                       parent
                            //                  [..., key, ...]
                            //                       /   \
                            //            [left child]   [...]
                            //           /            \
                            //        [...]         [..., key predecessor]
                            //
                            // In this case, we replace `key` with the key's predecessor from the
                            // left child's subtree, then we recursively delete the key's
                            // predecessor for the following end result:
                            //
                            //                       parent
                            //            [..., key predecessor, ...]
                            //                       /   \
                            //            [left child]   [...]
                            //           /            \
                            //        [...]          [...]

                            // Recursively delete the predecessor.
                            // TODO: do this in a single pass.
                            let predecessor = left_child.get_max(&self.memory);
                            self.remove_helper(node.children[idx], &predecessor.0)?;

                            // Replace the `key` with its predecessor.
                            node.swap_entry(idx, predecessor);

                            // Save the parent node.
                            node.save(&self.memory)?;
                            return Ok(Some(value));
                        }

                        // Check if the child that succeeds `key` has at least `B` keys.
                        let right_child = self.load_node(node.children[idx + 1]);
                        if right_child.entries.len() >= B as usize {
                            // Case 2.b: The node's right child has >= `B` keys.
                            //
                            //                       parent
                            //                  [..., key, ...]
                            //                       /   \
                            //                   [...]   [right child]
                            //                          /             \
                            //              [key successor, ...]     [...]
                            //
                            // In this case, we replace `key` with the key's successor from the
                            // right child's subtree, then we recursively delete the key's
                            // successor for the following end result:
                            //
                            //                       parent
                            //            [..., key successor, ...]
                            //                       /   \
                            //                  [...]   [right child]
                            //                           /            \
                            //                        [...]          [...]

                            // Recursively delete the successor.
                            // TODO: do this in a single pass.
                            let successor = right_child.get_min(&self.memory);
                            self.remove_helper(node.children[idx + 1], &successor.0)?;

                            // Replace the `key` with its successor.
                            node.swap_entry(idx, successor);

                            // Save the parent node.
                            node.save(&self.memory)?;
                            return Ok(Some(value));
                        }

                        // Case 2.c: Both the left child and right child have B - 1 keys.
                        //
                        //                       parent
                        //                  [..., key, ...]
                        //                       /   \
                        //            [left child]   [right child]
                        //
                        // In this case, we merge (left child, key, right child) into a single
                        // node of size 2B - 1. The result will look like this:
                        //
                        //                       parent
                        //                     [...  ...]
                        //                         |
                        //          [left child, `key`, right child] <= new child
                        //
                        // We then recurse on this new child to delete `key`.
                        //
                        // If `parent` becomes empty (which can only happen if it's the root),
                        // then `parent` is deleted and `new_child` becomes the new root.
                        debug_assert_eq!(left_child.entries.len(), B as usize - 1);
                        debug_assert_eq!(right_child.entries.len(), B as usize - 1);

                        // Merge the left and right children.
                        let new_child =
                            self.merge(right_child, left_child, node.entries.remove(idx))?;

                        // TODO: make removing entries + children more safe to not guarantee the
                        // invarian that len(children) = len(keys) + 1 and len(keys) = len(values)
                        // Remove the post child from the parent node.
                        node.children.remove(idx + 1);

                        if node.entries.is_empty() {
                            debug_assert_eq!(node.address, self.root_offset);

                            if node.address == self.root_offset {
                                debug_assert_eq!(node.children, vec![new_child.address]);
                                self.root_offset = new_child.address;

                                // FIXME: Add test case that covers this deallocation.
                                self.allocator.deallocate(node.address);
                            }
                        }

                        node.save(&self.memory)?;
                        new_child.save(&self.memory)?;

                        // Recursively delete the key.
                        self.remove_helper(new_child.address, key)
                    }
                    Err(idx) => {
                        // Case 3: The node is an internal node and the key does NOT exist in it.

                        // If the key does exist in the tree, it will exist in the subtree at index
                        // `idx`.
                        let mut child = self.load_node(node.children[idx]);

                        if child.entries.len() >= B as usize {
                            // The child has enough nodes. Recurse to delete the `key` from the
                            // `child`.
                            return self.remove_helper(node.children[idx], key);
                        }

                        // The child has < `B` keys. Let's see if it has a sibling with >= `B` keys.
                        let mut left_sibling = if idx > 0 {
                            Some(self.load_node(node.children[idx - 1]))
                        } else {
                            None
                        };

                        let mut right_sibling = if idx + 1 < node.children.len() {
                            Some(self.load_node(node.children[idx + 1]))
                        } else {
                            None
                        };

                        if let Some(ref mut left_sibling) = left_sibling {
                            if left_sibling.entries.len() >= B as usize {
                                // Case 3.a (left): The child has a left sibling with >= `B` keys.
                                //
                                //                            [d] (parent)
                                //                           /   \
                                //  (left sibling) [a, b, c]     [e, f] (child)
                                //                         \
                                //                         [c']
                                //
                                // In this case, we move a key down from the parent into the child
                                // and move a key from the left sibling up into the parent
                                // resulting in the following tree:
                                //
                                //                            [c] (parent)
                                //                           /   \
                                //       (left sibling) [a, b]   [d, e, f] (child)
                                //                              /
                                //                            [c']
                                //
                                // We then recurse to delete the key from the child.

                                // Remove the last entry from the left sibling.
                                let (left_sibling_key, left_sibling_value) =
                                    left_sibling.entries.pop().unwrap();

                                // Replace the parent's entry with the one from the left sibling.
                                let (parent_key, parent_value) = node
                                    .swap_entry(idx - 1, (left_sibling_key, left_sibling_value));

                                // Move the entry from the parent into the child.
                                child.entries.insert(0, (parent_key, parent_value));

                                // Move the last child from left sibling into child.
                                if let Some(last_child) = left_sibling.children.pop() {
                                    assert_eq!(left_sibling.node_type, NodeType::Internal);
                                    assert_eq!(child.node_type, NodeType::Internal);

                                    child.children.insert(0, last_child);
                                } else {
                                    assert_eq!(left_sibling.node_type, NodeType::Leaf);
                                    assert_eq!(child.node_type, NodeType::Leaf);
                                }

                                left_sibling.save(&self.memory)?;
                                child.save(&self.memory)?;
                                node.save(&self.memory)?;
                                return self.remove_helper(child.address, key);
                            }
                        }

                        if let Some(right_sibling) = &mut right_sibling {
                            if right_sibling.entries.len() >= B as usize {
                                // Case 3.a (right): The child has a right sibling with >= `B` keys.
                                //
                                //                            [c] (parent)
                                //                           /   \
                                //             (child) [a, b]     [d, e, f] (left sibling)
                                //                               /
                                //                            [d']
                                //
                                // In this case, we move a key down from the parent into the child
                                // and move a key from the right sibling up into the parent
                                // resulting in the following tree:
                                //
                                //                            [d] (parent)
                                //                           /   \
                                //          (child) [a, b, c]     [e, f] (right sibling)
                                //                          \
                                //                           [d']
                                //
                                // We then recurse to delete the key from the child.

                                // Remove the first entry from the right sibling.
                                let (right_sibling_key, right_sibling_value) =
                                    right_sibling.entries.remove(0);

                                // Replace the parent's entry with the one from the right sibling.
                                let parent_entry =
                                    node.swap_entry(idx, (right_sibling_key, right_sibling_value));

                                // Move the entry from the parent into the child.
                                child.entries.push(parent_entry);

                                // Move the first child of right_sibling into subtree.
                                match right_sibling.node_type {
                                    NodeType::Internal => {
                                        assert_eq!(child.node_type, NodeType::Internal);
                                        child.children.push(right_sibling.children.remove(0));
                                    }
                                    NodeType::Leaf => {
                                        assert_eq!(child.node_type, NodeType::Leaf);
                                    }
                                }

                                right_sibling.save(&self.memory)?;
                                child.save(&self.memory)?;
                                node.save(&self.memory)?;
                                return self.remove_helper(child.address, key);
                            }
                        }

                        // Case 3.b: neither siblings of the child have >= `B` keys.

                        // Merge
                        if let Some(left_sibling) = left_sibling {
                            println!("merging into left");
                            // Merge child into left sibling.

                            let left_sibling_address = left_sibling.address;
                            println!("MERGE LEFT");
                            self.merge(child, left_sibling, node.entries.remove(idx - 1))?;
                            // Removing child from parent.
                            node.children.remove(idx);

                            if node.entries.is_empty() {
                                println!("DEALLOCATE 2");
                                self.allocator.deallocate(node.address);

                                if node.address == self.root_offset {
                                    println!("updating root address");
                                    // Update the root.
                                    self.root_offset = left_sibling_address;
                                }
                            } else {
                                node.save(&self.memory)?;
                            }

                            return self.remove_helper(left_sibling_address, key);
                        }

                        if let Some(right_sibling) = right_sibling {
                            println!("merging into right");
                            // Merge child into right sibling.

                            let right_sibling_address = right_sibling.address;
                            println!("MERGE RIGHT");
                            self.merge(child, right_sibling, node.entries.remove(idx))?;

                            // Removing child from parent.
                            node.children.remove(idx);

                            if node.entries.is_empty() {
                                println!("DEALLOCATE3");
                                self.allocator.deallocate(node.address);

                                if node.address == self.root_offset {
                                    println!("updating root address");
                                    // Update the root.
                                    self.root_offset = right_sibling_address;
                                }
                            } else {
                                node.save(&self.memory)?;
                            }

                            return self.remove_helper(right_sibling_address, key);
                        }

                        unreachable!("at least one of the siblings must exist");
                    }
                }
            }
        }
    }

    fn merge(
        &mut self,
        source: Node,
        into: Node,
        median: (Key, Value),
    ) -> Result<Node, WriteError> {
        // TODO: assert that source and into are non-empty.
        // TODO: assert that both types are the same.
        let into_address = into.address;
        let source_address = source.address;

        // Figure out which node contains lower values than the other.
        let (mut lower, mut higher) = if source.entries[0].0 < into.entries[0].0 {
            (source, into)
        } else {
            (into, source)
        };

        lower.entries.push(median);

        lower.entries.append(&mut higher.entries);

        lower.address = into_address;

        // Move the children (if any exist).
        lower.children.append(&mut higher.children);

        lower.save(&self.memory)?;

        println!("DEALLOCATE4");
        self.allocator.deallocate(source_address);
        Ok(lower)
    }

    fn allocate_node(&mut self, node_type: NodeType) -> Node {
        //let node_header_len = core::mem::size_of::<NodeHeader>() as u64;
        //let node_size = node_header_len + CAPACITY * ((MAX_KEY_SIZE + MAX_VALUE_SIZE) as u64);
        Node {
            address: self.allocator.allocate().unwrap(),
            entries: vec![],
            children: vec![],
            node_type,
            max_key_size: self.max_key_size,
            max_value_size: self.max_value_size,
        }
    }

    fn load_node(&self, address: Ptr) -> Node {
        Node::load(
            address,
            &self.memory,
            self.max_key_size,
            self.max_value_size,
        )
    }

    // Takes as input a nonfull internal `node` and index to its full child, then
    // splits this child into two, adding an additional child to `node`.
    //
    // Example:
    //
    //                          [ ... M   Y ... ]
    //                                  |
    //                 [ N  O  P  Q  R  S  T  U  V  W  X ]
    //
    //
    // After splitting becomes:
    //
    //                         [ ... M  S  Y ... ]
    //                                 / \
    //                [ N  O  P  Q  R ]   [ T  U  V  W  X ]
    //
    fn split_child(&mut self, node: &mut Node, full_child_idx: usize) -> Result<(), WriteError> {
        // The node must not be full.
        assert!(!node.is_full());

        // The node's child must be full.
        let mut full_child = self.load_node(node.children[full_child_idx]);
        assert!(full_child.is_full());

        // Create a sibling to this full child (which has to be the same type).
        let mut sibling = self.allocate_node(full_child.node_type);

        // Move the values above the median into the new sibling.
        sibling.entries = full_child.entries.split_off(B as usize);

        if full_child.node_type == NodeType::Internal {
            sibling.children = full_child.children.split_off(B as usize);
        }

        // Add sibling as a new child in the node.
        node.children.insert(full_child_idx + 1, sibling.address);

        // Move the median entry into the node.
        let (median_key, median_value) = full_child.entries.pop().unwrap();
        node.entries
            .insert(full_child_idx, (median_key, median_value));

        sibling.save(&self.memory)?;
        full_child.save(&self.memory)?;
        node.save(&self.memory)?;
        Ok(())
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

#[derive(Debug, PartialEq)]
pub enum InsertError {
    KeyTooLarge { given: usize, max: usize },
    ValueTooLarge { given: usize, max: usize },
    WriteError(WriteError),
}

impl From<WriteError> for InsertError {
    fn from(err: WriteError) -> Self {
        Self::WriteError(err)
    }
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
    fn insert_get() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 3, 4).unwrap();

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), Ok(None));
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![4, 5, 6]));
    }

    #[test]
    fn insert_overwrites_previous_value() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), Ok(None));
        assert_eq!(
            btree.insert(vec![1, 2, 3], vec![7, 8, 9]),
            Ok(Some(vec![4, 5, 6]))
        );
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![7, 8, 9]));
    }

    #[test]
    fn insert_get_multiple() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), Ok(None));
        assert_eq!(btree.insert(vec![4, 5], vec![7, 8, 9, 10]), Ok(None));
        assert_eq!(btree.insert(vec![], vec![11]), Ok(None));
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![4, 5, 6]));
        assert_eq!(btree.get(&vec![4, 5]), Some(vec![7, 8, 9, 10]));
        assert_eq!(btree.get(&vec![]), Some(vec![11]));
    }

    #[test]
    fn allocations() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 0..CAPACITY as u8 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }

        // Only need a single allocation to store up to `CAPACITY` elements.
        assert_eq!(btree.allocator.num_allocations(), 1);

        assert_eq!(btree.insert(vec![255], vec![]), Ok(None));

        // The node had to be split into three nodes.
        assert_eq!(btree.allocator.num_allocations(), 3);
    }

    #[test]
    fn allocations_2() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();
        assert_eq!(btree.allocator.num_allocations(), 0);

        assert_eq!(btree.insert(vec![], vec![]), Ok(None));
        assert_eq!(btree.allocator.num_allocations(), 1);

        assert_eq!(btree.remove(&vec![]), Ok(Some(vec![])));
        assert_eq!(btree.allocator.num_allocations(), 0);
    }

    #[test]
    fn insert_same_key_multiple() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        assert_eq!(btree.insert(vec![1], vec![2]), Ok(None));

        for i in 2..10 {
            assert_eq!(btree.insert(vec![1], vec![i + 1]), Ok(Some(vec![i])));
        }
    }

    #[test]
    fn insert_split_node() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }

        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![]), Ok(None));

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&vec![i]), Some(vec![]));
        }
    }

    #[test]
    fn insert_split_multiple_nodes() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }
        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![]), Ok(None));

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Internal);
        assert_eq!(root.entries, vec![(vec![6], vec![])]);
        assert_eq!(root.children.len(), 2);

        let child_0 = btree.load_node(root.children[0]);
        assert_eq!(child_0.node_type, NodeType::Leaf);
        assert_eq!(
            child_0.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![])
            ]
        );

        let child_1 = btree.load_node(root.children[1]);
        assert_eq!(child_1.node_type, NodeType::Leaf);
        assert_eq!(
            child_1.entries,
            vec![
                (vec![7], vec![]),
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![])
            ]
        );

        for i in 1..=12 {
            assert_eq!(btree.get(&vec![i]), Some(vec![]));
        }

        // Insert more to cause more splitting.
        assert_eq!(btree.insert(vec![13], vec![]), Ok(None));
        assert_eq!(btree.insert(vec![14], vec![]), Ok(None));
        assert_eq!(btree.insert(vec![15], vec![]), Ok(None));
        assert_eq!(btree.insert(vec![16], vec![]), Ok(None));
        assert_eq!(btree.insert(vec![17], vec![]), Ok(None));
        // Should cause another split
        assert_eq!(btree.insert(vec![18], vec![]), Ok(None));

        for i in 1..=18 {
            assert_eq!(btree.get(&vec![i]), Some(vec![]));
        }

        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Internal);
        assert_eq!(root.entries, vec![(vec![6], vec![]), (vec![12], vec![])]);
        assert_eq!(root.children.len(), 3);

        let child_0 = btree.load_node(root.children[0]);
        assert_eq!(child_0.node_type, NodeType::Leaf);
        assert_eq!(
            child_0.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![])
            ]
        );

        let child_1 = btree.load_node(root.children[1]);
        assert_eq!(child_1.node_type, NodeType::Leaf);
        assert_eq!(
            child_1.entries,
            vec![
                (vec![7], vec![]),
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
            ]
        );

        let child_2 = btree.load_node(root.children[2]);
        assert_eq!(child_2.node_type, NodeType::Leaf);
        assert_eq!(
            child_2.entries,
            vec![
                (vec![13], vec![]),
                (vec![14], vec![]),
                (vec![15], vec![]),
                (vec![16], vec![]),
                (vec![17], vec![]),
                (vec![18], vec![]),
            ]
        );
    }

    #[test]
    fn remove_simple() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), Ok(None));
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![4, 5, 6]));
        assert_eq!(btree.remove(&vec![1, 2, 3]), Ok(Some(vec![4, 5, 6])));
        assert_eq!(btree.get(&vec![1, 2, 3]), None);
    }

    #[test]
    fn remove_split_node() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }
        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![]), Ok(None));

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&vec![i]), Some(vec![]));
        }

        // Remove node 6. Triggers case 2.b
        assert_eq!(btree.remove(&vec![6]), Ok(Some(vec![])));

        // The result should looks like this:
        //                [7]
        //               /   \
        // [1, 2, 3, 4, 5]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Internal);
        assert_eq!(root.entries, vec![(vec![7], vec![])]);
        assert_eq!(root.children.len(), 2);

        let child_0 = btree.load_node(root.children[0]);
        assert_eq!(child_0.node_type, NodeType::Leaf);
        assert_eq!(
            child_0.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![])
            ]
        );

        let child_1 = btree.load_node(root.children[1]);
        assert_eq!(child_1.node_type, NodeType::Leaf);
        assert_eq!(
            child_1.entries,
            vec![
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![])
            ]
        );

        // Remove node 7. Triggers case 2.c
        assert_eq!(btree.remove(&vec![7]), Ok(Some(vec![])));
        // The result should looks like this:
        //
        // [1, 2, 3, 4, 5, 8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Leaf);
        assert_eq!(
            root.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![]),
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![])
            ]
        );
    }

    #[test]
    fn remove_split_node_2() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![2]), Ok(None));
        }
        // Should now split a node.
        assert_eq!(btree.insert(vec![0], vec![2]), Ok(None));

        // The result should looks like this:
        //                    [6]
        //                   /   \
        // [0, 1, 2, 3, 4, 5]     [7, 8, 9, 10, 11]

        for i in 0..=11 {
            assert_eq!(btree.get(&vec![i]), Some(vec![2]));
        }

        // Remove node 6. Triggers case 2.a
        assert_eq!(btree.remove(&vec![6]), Ok(Some(vec![2])));

        /*
        // The result should looks like this:
        //                [5]
        //               /   \
        // [0, 1, 2, 3, 4]   [7, 8, 9, 10, 11]
        let root = btree.load_node(btree.root_offset);
        match root {
            Node::Internal(internal) => {
                assert_eq!(internal.keys, vec![vec![5]]);
                assert_eq!(internal.values, vec![vec![2]]);
                assert_eq!(internal.children.len(), 2);

                let child_0 = Node::load(internal.children[0], &mem);
                match child_0 {
                    Node::Leaf(leaf) => {
                        assert_eq!(leaf.keys, vec![vec![0], vec![1], vec![2], vec![3], vec![4]]);
                        assert_eq!(
                            leaf.values(),
                            vec![vec![2], vec![2], vec![2], vec![2], vec![2]]
                        );
                    }
                    _ => panic!("child should be leaf"),
                }

                let child_1 = Node::load(internal.children[1], &mem);
                match child_1 {
                    Node::Leaf(leaf) => {
                        assert_eq!(
                            leaf.keys,
                            vec![vec![7], vec![8], vec![9], vec![10], vec![11]]
                        );
                        assert_eq!(
                            leaf.values(),
                            vec![vec![2], vec![2], vec![2], vec![2], vec![2]]
                        );
                    }
                    _ => panic!("child should be leaf"),
                }
            }
            _ => panic!("root should be internal"),
        }*/
    }

    #[test]
    fn reloading() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), Ok(None));

        let mut btree = StableBTreeMap::load(mem.clone()).unwrap();
        assert_eq!(btree.get(&vec![1, 2, 3]), Some(vec![4, 5, 6]));

        let mut btree = StableBTreeMap::load(mem.clone()).unwrap();
        assert_eq!(btree.remove(&vec![1, 2, 3]), Ok(Some(vec![4, 5, 6])));

        let mut btree = StableBTreeMap::load(mem.clone()).unwrap();
        assert_eq!(btree.get(&vec![1, 2, 3]), None);
    }

    #[test]
    fn remove_3a_right() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }
        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![]), Ok(None));

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        // Remove node 3. Triggers case 3.a
        assert_eq!(btree.remove(&vec![3]), Ok(Some(vec![])));

        // The result should looks like this:
        //                [7]
        //               /   \
        // [1, 2, 4, 5, 6]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Internal);
        assert_eq!(root.entries, vec![(vec![7], vec![])]);
        assert_eq!(root.children.len(), 2);

        let child_0 = btree.load_node(root.children[0]);
        assert_eq!(child_0.node_type, NodeType::Leaf);
        assert_eq!(
            child_0.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![]),
                (vec![6], vec![]),
            ]
        );

        let child_1 = btree.load_node(root.children[1]);
        assert_eq!(child_1.node_type, NodeType::Leaf);
        assert_eq!(
            child_1.entries,
            vec![
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![]),
            ]
        );
    }

    #[test]
    fn remove_3a_left() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }
        // Should now split a node.
        assert_eq!(btree.insert(vec![0], vec![]), Ok(None));

        // The result should looks like this:
        //                   [6]
        //                  /   \
        // [0, 1, 2, 3, 4, 5]   [7, 8, 9, 10, 11]

        // Remove node 8. Triggers case 3.a left
        assert_eq!(btree.remove(&vec![8]), Ok(Some(vec![])));

        // The result should looks like this:
        //                [5]
        //               /   \
        // [0, 1, 2, 3, 4]   [6, 7, 9, 10, 11]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Internal);
        assert_eq!(root.entries, vec![(vec![5], vec![])]);
        assert_eq!(root.children.len(), 2);

        let child_0 = btree.load_node(root.children[0]);
        assert_eq!(child_0.node_type, NodeType::Leaf);
        assert_eq!(
            child_0.entries,
            vec![
                (vec![0], vec![]),
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
            ]
        );

        let child_1 = btree.load_node(root.children[1]);
        assert_eq!(child_1.node_type, NodeType::Leaf);
        assert_eq!(
            child_1.entries,
            vec![
                (vec![6], vec![]),
                (vec![7], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
            ]
        );
    }

    #[test]
    fn remove_3b_merge_into_right() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }
        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![]), Ok(None));

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&vec![i]), Some(vec![]));
        }

        // Remove node 6. Triggers case 2.b
        assert_eq!(btree.remove(&vec![6]), Ok(Some(vec![])));
        // The result should looks like this:
        //                [7]
        //               /   \
        // [1, 2, 3, 4, 5]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Internal);
        assert_eq!(root.entries, vec![(vec![7], vec![])]);
        assert_eq!(root.children.len(), 2);

        let child_0 = btree.load_node(root.children[0]);
        assert_eq!(child_0.node_type, NodeType::Leaf);
        assert_eq!(
            child_0.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![]),
            ]
        );

        let child_1 = btree.load_node(root.children[1]);
        assert_eq!(child_1.node_type, NodeType::Leaf);
        assert_eq!(
            child_1.entries,
            vec![
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![]),
            ]
        );

        // Remove node 3. Triggers case 3.b
        assert_eq!(btree.remove(&vec![3]), Ok(Some(vec![])));

        // The result should looks like this:
        //
        // [1, 2, 4, 5, 7, 8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Leaf);
        assert_eq!(
            root.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![]),
                (vec![7], vec![]),
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![])
            ]
        );
    }

    #[test]
    fn remove_3b_merge_into_left() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![]), Ok(None));
        }

        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![]), Ok(None));

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=12 {
            assert_eq!(btree.get(&vec![i]), Some(vec![]));
        }

        // Remove node 6. Triggers case 2.b
        assert_eq!(btree.remove(&vec![6]), Ok(Some(vec![])));

        // The result should looks like this:
        //                [7]
        //               /   \
        // [1, 2, 3, 4, 5]   [8, 9, 10, 11, 12]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Internal);
        assert_eq!(root.entries, vec![(vec![7], vec![])]);
        assert_eq!(root.children.len(), 2);

        let child_0 = btree.load_node(root.children[0]);
        assert_eq!(child_0.node_type, NodeType::Leaf);
        assert_eq!(
            child_0.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![]),
            ]
        );

        let child_1 = btree.load_node(root.children[1]);
        assert_eq!(child_1.node_type, NodeType::Leaf);
        assert_eq!(
            child_1.entries,
            vec![
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![10], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![]),
            ]
        );

        // Remove node 10. Triggers case 3.b where we merge the right into the left.
        assert_eq!(btree.remove(&vec![10]), Ok(Some(vec![])));

        // The result should looks like this:
        //
        // [1, 2, 3, 4, 5, 7, 8, 9, 11, 12]
        let root = btree.load_node(btree.root_offset);
        assert_eq!(root.node_type, NodeType::Leaf);
        assert_eq!(
            root.entries,
            vec![
                (vec![1], vec![]),
                (vec![2], vec![]),
                (vec![3], vec![]),
                (vec![4], vec![]),
                (vec![5], vec![]),
                (vec![7], vec![]),
                (vec![8], vec![]),
                (vec![9], vec![]),
                (vec![11], vec![]),
                (vec![12], vec![]),
            ]
        );
    }

    #[test]
    fn many_insertions() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for j in 0..=10 {
            for i in 0..=255 {
                assert_eq!(btree.insert(vec![i, j], vec![i, j]), Ok(None));
            }
        }

        for j in 0..=10 {
            for i in 0..=255 {
                assert_eq!(btree.get(&vec![i, j]), Some(vec![i, j]));
            }
        }

        let mut btree = StableBTreeMap::load(mem.clone()).unwrap();

        for j in 0..=10 {
            for i in 0..=255 {
                println!("i, j: {}, {}", i, j);
                assert_eq!(btree.remove(&vec![i, j]), Ok(Some(vec![i, j])));
            }
        }

        for j in 0..=10 {
            for i in 0..=255 {
                assert_eq!(btree.get(&vec![i, j]), None);
            }
        }

        // We've deallocated everything we allocated.
        assert_eq!(btree.allocator.num_allocations(), 0);
    }

    #[test]
    fn many_insertions_2() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for j in (0..=10).rev() {
            for i in (0..=255).rev() {
                assert_eq!(btree.insert(vec![i, j], vec![i, j]), Ok(None));
            }
        }

        for j in 0..=10 {
            for i in 0..=255 {
                assert_eq!(btree.get(&vec![i, j]), Some(vec![i, j]));
            }
        }

        let mut btree = StableBTreeMap::load(mem.clone()).unwrap();

        for j in (0..=10).rev() {
            for i in (0..=255).rev() {
                assert_eq!(btree.remove(&vec![i, j]), Ok(Some(vec![i, j])));
            }
        }

        for j in 0..=10 {
            for i in 0..=255 {
                assert_eq!(btree.get(&vec![i, j]), None);
            }
        }

        // We've deallocated everything we allocated.
        assert_eq!(btree.allocator.num_allocations(), 0);
    }

    /*
    #[test]
    fn deallocating() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5);

        let old_free_list = btree.free_list;

        assert_eq!(btree.insert(vec![1, 2, 3], vec![4, 5, 6]), None);
        assert_eq!(btree.remove(&vec![1, 2, 3]), Some(vec![4, 5, 6]));

        // Added an element and removed it. The free list should be unchanged.
        assert_eq!(old_free_list, btree.free_list);
    }*/
}

#[cfg(test)]
mod remove {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    fn case_1() {
        let mem = make_memory();
        let mut btree = StableBTreeMap::new(mem.clone(), 5, 5).unwrap();

        for i in 1..=11 {
            assert_eq!(btree.insert(vec![i], vec![2]), Ok(None));
        }

        // Should now split a node.
        assert_eq!(btree.insert(vec![12], vec![2]), Ok(None));

        // The result should looks like this:
        //                [6]
        //               /   \
        // [1, 2, 3, 4, 5]   [7, 8, 9, 10, 11, 12]

        for i in 1..=5 {
            assert_eq!(btree.remove(&vec![i]), Ok(Some(vec![2])));
        }
    }
}
