//! This module implements a growable array in stable memory.

use crate::base_vec::BaseVec;
pub use crate::base_vec::InitError;
use crate::storable::Storable;
use crate::{GrowFailed, Memory};
use std::fmt;

#[cfg(test)]
mod tests;

const MAGIC: [u8; 3] = *b"SVC"; // Short for "stable vector".

/// An implementation of growable arrays in stable memory.
pub struct Vec<T: Storable, M: Memory>(BaseVec<T, M>);

impl<T: Storable, M: Memory> Vec<T, M> {
    /// Creates a new empty vector in the specified memory,
    /// overwriting any data structures the memory might have
    /// contained previously.
    ///
    /// Complexity: O(1)
    pub fn new(memory: M) -> Result<Self, GrowFailed> {
        BaseVec::<T, M>::new(memory, MAGIC).map(Self)
    }

    /// Initializes a vector in the specified memory.
    ///
    /// Complexity: O(1)
    ///
    /// PRECONDITION: the memory is either empty or contains a valid
    /// stable vector.
    pub fn init(memory: M) -> Result<Self, InitError> {
        BaseVec::<T, M>::init(memory, MAGIC).map(Self)
    }

    /// Returns the underlying memory instance.
    pub fn into_memory(self) -> M {
        self.0.into_memory()
    }

    /// Returns true if the vector is empty.
    ///
    /// Complexity: O(1)
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of items in the vector.
    ///
    /// Complexity: O(1)
    pub fn len(&self) -> u64 {
        self.0.len()
    }

    /// Sets the item at the specified index to the specified value.
    ///
    /// Complexity: O(max_size(T))
    ///
    /// PRECONDITION: index < self.len()
    pub fn set(&self, index: u64, item: &T) {
        self.0.set(index, item)
    }

    /// Returns the item at the specified index.
    ///
    /// Complexity: O(max_size(T))
    pub fn get(&self, index: u64) -> Option<T> {
        self.0.get(index)
    }

    /// Adds a new item at the end of the vector.
    ///
    /// Complexity: O(max_size(T))
    pub fn push(&self, item: &T) -> Result<(), GrowFailed> {
        self.0.push(item)
    }

    /// Removes the item at the end of the vector.
    ///
    /// Complexity: O(max_size(T))
    pub fn pop(&self) -> Option<T> {
        self.0.pop()
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = T> + '_ {
        self.0.iter()
    }

    #[cfg(test)]
    fn to_vec(&self) -> std::vec::Vec<T> {
        self.0.to_vec()
    }
}

impl<T: Storable + fmt::Debug, M: Memory> fmt::Debug for Vec<T, M> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(fmt)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// Creates a new shared memory instance.
    fn make_memory() -> Rc<RefCell<std::vec::Vec<u8>>> {
        Rc::new(RefCell::new(std::vec::Vec::new()))
    }

    #[test]
    fn api_conformance() {
        let mem = make_memory();
        let stable = Vec::new(mem).unwrap();
        let mut std = std::vec::Vec::new();

        let n = 10_u32;

        // Push elements.
        for i in 0..n {
            stable.push(&i).expect("stable.push failed");
            std.push(i);
        }

        // Length and emptiness.
        assert_eq!(stable.len(), std.len() as u64);
        assert_eq!(stable.is_empty(), std.is_empty());

        // Get by index.
        for i in 0..n {
            assert_eq!(stable.get(i as u64), Some(std[i as usize]));
        }

        // Set by index (stable.set is &mut self, std Vec uses indexing).
        for i in 0..n {
            let value = i * 10;
            stable.set(i as u64, &value);
            std[i as usize] = value;
        }

        // Confirm updated values.
        for i in 0..n {
            assert_eq!(stable.get(i as u64), Some(std[i as usize]));
        }

        // Pop elements.
        for _ in 0..n {
            assert_eq!(stable.pop(), std.pop());
        }

        // After popping everything, both should be empty.
        assert_eq!(stable.len(), 0);
        assert!(stable.is_empty());
        assert!(std.is_empty());
    }
}
