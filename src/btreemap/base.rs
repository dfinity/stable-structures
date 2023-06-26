use super::allocator::Allocator;
use crate::{
    types::{Address, Bytes, NULL},
    BoundedStorable, Memory, Storable,
};
//pub use iter::Iter;
//use iter::{Cursor, Index};
use crate::btreemap::bounded_btreemap::node::{Entry, Node, NodeType};
use std::borrow::Cow;
use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};

const MAGIC: &[u8; 3] = b"BTR";
const LAYOUT_VERSION: u8 = 1;
/// The sum of all the header fields, i.e. size of a packed header.
const PACKED_HEADER_SIZE: usize = 28;
/// The offset where the allocator begins.
const ALLOCATOR_OFFSET: usize = 52;

// XXX: not public outside of this crate
pub trait BaseBTreeMapSave<M: Memory> {
    fn save(&self, memory: &M, address: Address, length: u64) -> ();
}

pub trait NodeMethods<M: Memory, K: Storable + Ord + Clone> {
    fn allocate(&self, node_type: NodeType, allocator: &mut Allocator<M>) -> Node<K>;
    fn load(&self, address: Address, memory: &M) -> Node<K>;
}

/// A key/value store based on a B-Tree in stable memory.
/// In this version, both keys and values are bounded in size.
///
/// The implementation is based on the algorithm outlined in "Introduction to Algorithms"
/// by Cormen et al.
pub struct BaseBTreeMap<K, V, M, SaveFn, N>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
    N: NodeMethods<M, K>,
    SaveFn: BaseBTreeMapSave<M>,
{
    // XXX: make all these fields private if possible.
    // The address of the root node. If a root node doesn't exist, the address
    // is set to NULL.
    pub root_addr: Address,

    // An allocator used for managing memory and allocating nodes.
    pub allocator: Allocator<M>,

    // The number of elements in the map.
    pub length: u64,

    saver: SaveFn,

    node_methods: N,

    // A marker to communicate to the Rust compiler that we own these types.
    pub _phantom: PhantomData<(K, V)>,
}

impl<K, V, M, SaveFn, N> BaseBTreeMap<K, V, M, SaveFn, N>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
    SaveFn: BaseBTreeMapSave<M>,
    N: NodeMethods<M, K>,
{
    /// Creates a new instance a `BTreeMap`.
    ///
    /// The given `memory` is assumed to be exclusively reserved for this data
    /// structure and that it starts at address zero. Typically `memory` will
    /// be an instance of `RestrictedMemory`.
    ///
    /// When initialized, the data structure has the following memory layout:
    ///
    ///    |  BTreeHeader  |  Allocator | ... free memory for nodes |
    ///
    /// See `Allocator` for more details on its own memory layout.
    pub fn new(memory: M, page_size: Bytes, saver: SaveFn, node_methods: N) -> Self {
        let btree = Self {
            root_addr: NULL,
            allocator: Allocator::new(memory, Address::from(ALLOCATOR_OFFSET as u64), page_size),
            length: 0,
            saver,
            node_methods,
            _phantom: PhantomData,
        };

        btree.save();
        btree
    }

    pub fn load(memory: M, root_addr: Address, length: u64, saver: SaveFn, node_methods: N) -> Self {
        let allocator_addr = Address::from(ALLOCATOR_OFFSET as u64);
        Self {
            root_addr: root_addr,
            allocator: Allocator::load(memory, allocator_addr),
            length: length,
            saver,
            node_methods,
            _phantom: PhantomData,
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// The previous value of the key, if present, is returned.
    ///
    /// PRECONDITION:
    ///   key.to_bytes().len() <= Key::MAX_SIZE
    ///   value.to_bytes().len() <= Value::MAX_SIZE
    pub fn insert(
        &mut self,
        key: K,
        value: V,
    ) -> Option<V> {
        /*let key_bytes = key.to_bytes();
        let value_bytes = value.to_bytes();

        assert!(
            key_bytes.len() <= self.max_key_size as usize,
            "Key is too large. Expected <= {} bytes, found {} bytes",
            self.max_key_size,
            key_bytes.len()
        );

        assert!(
            value_bytes.len() <= self.max_value_size as usize,
            "Value is too large. Expected <= {} bytes, found {} bytes",
            self.max_value_size,
            value_bytes.len()
        );*/

        let value_bytes = value.to_bytes();
        let value = value_bytes.to_vec();

        let root = if self.root_addr == NULL {
            // No root present. Allocate one.
            let node = self.node_methods.allocate(NodeType::Leaf, &mut self.allocator);
            self.root_addr = node.address();
            self.save();
            node
        } else {
            // Load the root from memory.
            let mut root = self.node_methods.load(self.root_addr, self.memory());

            // Check if the key already exists in the root.
            if let Ok(idx) = root.search(&key) {
                // The key exists. Overwrite it and return the previous value.
                let (_, previous_value) = root.swap_entry(idx, (key, value), self.memory());
                root.save(self.memory());
                return Some(V::from_bytes(Cow::Owned(previous_value)));
            }

            // If the root is full, we need to introduce a new node as the root.
            //
            // NOTE: In the case where we are overwriting an existing key, then introducing
            // a new root node isn't strictly necessary. However, that's a micro-optimization
            // that adds more complexity than it's worth.
            if root.is_full() {
                // The root is full. Allocate a new node that will be used as the new root.
                let mut new_root = self.node_methods.allocate(NodeType::Internal, &mut self.allocator);

                // The new root has the old root as its only child.
                new_root.push_child(self.root_addr);

                // Update the root address.
                self.root_addr = new_root.address();
                self.save();

                // Split the old (full) root.
                self.split_child(&mut new_root, 0);

                new_root
            } else {
                root
            }
        };

        self.insert_nonfull(root, key, value)
            .map(Cow::Owned)
            .map(V::from_bytes)
    }

    /// Returns the value associated with the given key if it exists.
    pub fn get(&self, key: &K) -> Option<V> {
        if self.root_addr == NULL {
            return None;
        }

        self.get_helper(self.root_addr, key)
            .map(Cow::Owned)
            .map(V::from_bytes)
    }

    fn get_helper(
        &self,
        node_addr: Address,
        key: &K,
    ) -> Option<Vec<u8>> {
        let node = self.node_methods.load(node_addr, self.memory());
        match node.search(key) {
            Ok(idx) => Some(node.value(idx, self.memory()).to_vec()),
            Err(idx) => {
                match node.node_type() {
                    NodeType::Leaf => None, // Key not found.
                    NodeType::Internal => {
                        // The key isn't in the node. Look for the key in the child.
                        self.get_helper(node.child(idx), key)
                    }
                }
            }
        }
    }

    // Inserts an entry into a node that is *not full*.
    fn insert_nonfull(
        &mut self,
        mut node: Node<K>,
        key: K,
        value: Vec<u8>,
    ) -> Option<Vec<u8>> {
        // We're guaranteed by the caller that the provided node is not full.
        assert!(!node.is_full());

        // Look for the key in the node.
        match node.search(&key) {
            Ok(idx) => {
                // The key is already in the node.
                // Overwrite it and return the previous value.
                let (_, previous_value) = node.swap_entry(idx, (key, value), self.memory());

                node.save(self.memory());
                Some(previous_value)
            }
            Err(idx) => {
                // The key isn't in the node. `idx` is where that key should be inserted.

                match node.node_type() {
                    NodeType::Leaf => {
                        // The node is a non-full leaf.
                        // Insert the entry at the proper location.
                        node.insert_entry(idx, (key, value));
                        node.save(self.memory());

                        // Update the length.
                        self.length += 1;
                        self.save();

                        // No previous value to return.
                        None
                    }
                    NodeType::Internal => {
                        // The node is an internal node.
                        // Load the child that we should add the entry to.
                        let mut child = self.node_methods.load(node.child(idx), self.memory());

                        if child.is_full() {
                            // Check if the key already exists in the child.
                            if let Ok(idx) = child.search(&key) {
                                // The key exists. Overwrite it and return the previous value.
                                let (_, previous_value) =
                                    child.swap_entry(idx, (key, value), self.memory());
                                child.save(self.memory());
                                return Some(previous_value);
                            }

                            // The child is full. Split the child.
                            self.split_child(&mut node, idx);

                            // The children have now changed. Search again for
                            // the child where we need to store the entry in.
                            let idx = node.search(&key).unwrap_or_else(|idx| idx);
                            child = self.node_methods.load(node.child(idx), self.memory());
                        }

                        // The child should now be not full.
                        assert!(!child.is_full());

                        self.insert_nonfull(child, key, value)
                    }
                }
            }
        }
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
    fn split_child(
        &mut self,
        node: &mut Node<K>,
        full_child_idx: usize,
    ) {
        // The node must not be full.
        assert!(!node.is_full());

        // The node's child must be full.
        let mut full_child = self.node_methods.load(node.child(full_child_idx), self.memory());
        assert!(full_child.is_full());

        // Create a sibling to this full child (which has to be the same type).
        let mut sibling = self.node_methods.allocate(full_child.node_type(), &mut self.allocator);
        assert_eq!(sibling.node_type(), full_child.node_type());

        // Add sibling as a new child in the node.
        node.insert_child(full_child_idx + 1, sibling.address());

        let (median_key, median_value) = full_child.split(&mut sibling, self.memory());

        node.insert_entry(full_child_idx, (median_key, median_value));

        sibling.save(self.memory());
        full_child.save(self.memory());
        node.save(self.memory());
    }

    fn memory(&self) -> &M {
        self.allocator.memory()
    }

    fn save(&self) {
        self.saver.save(self.memory(), self.root_addr, self.length);
    }
}
