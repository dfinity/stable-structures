//! This module implements a growable array in stable memory.

use crate::base_vec::BaseVec;
pub use crate::base_vec::InitError;
use crate::storable::BoundedStorable;
use crate::{GrowFailed, Memory};
use std::fmt;

#[cfg(test)]
mod tests;

const MAGIC: [u8; 3] = *b"SVC"; // Short for "stable vector".

/// An implementation of growable arrays in stable memory.
pub struct Vec<T: BoundedStorable, M: Memory>(BaseVec<T, M>);

impl<T: BoundedStorable, M: Memory> Vec<T, M> {
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
    /// Complexity: O(T::MAX_SIZE)
    ///
    /// PRECONDITION: index < self.len()
    pub fn set(&self, index: u64, item: &T) {
        self.0.set(index, item)
    }

    /// Returns the item at the specified index.
    ///
    /// Complexity: O(T::MAX_SIZE)
    pub fn get(&self, index: u64) -> Option<T> {
        self.0.get(index)
    }

    /// Adds a new item at the end of the vector.
    ///
    /// Complexity: O(T::MAX_SIZE)
    pub fn push(&self, item: &T) -> Result<(), GrowFailed> {
        self.0.push(item)
    }

    /// Removes the item at the end of the vector.
    ///
    /// Complexity: O(T::MAX_SIZE)
    pub fn pop(&self) -> Option<T> {
        self.0.pop()
    }

    pub fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.0.iter()
    }

    #[cfg(test)]
    fn to_vec(&self) -> std::vec::Vec<T> {
        self.0.to_vec()
    }
}

impl<T: BoundedStorable + fmt::Debug, M: Memory> fmt::Debug for Vec<T, M> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(fmt)
    }
}
