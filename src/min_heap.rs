use crate::base_vec::{BaseVec, InitError};
use crate::storable::BoundedStorable;
use crate::{GrowFailed, Memory};

const MAGIC: [u8; 3] = *b"SHP"; // Short for "stable heap".

/// An implementation of a binary heap.
///
/// Contrary to [std::collections::BinaryHeap], this heap is a min-heap (smallest items come first).
/// Motivation: max heaps are helpful for sorting, but most daily programming tasks require min
/// heaps.
pub struct MinHeap<T: BoundedStorable + PartialOrd, M: Memory>(BaseVec<T, M>);

impl<T, M> MinHeap<T, M>
where
    T: BoundedStorable + PartialOrd,
    M: Memory,
{
    /// Creates a new empty heap in the specified memory,
    /// overwriting any data structures the memory might have
    /// contained.
    ///
    /// Complexity: O(1)
    pub fn new(memory: M) -> Result<Self, GrowFailed> {
        BaseVec::<T, M>::new(memory, MAGIC).map(Self)
    }

    /// Initializes a heap in the specified memory.
    ///
    /// Complexity: O(1)
    ///
    /// PRECONDITION: the memory is either empty or contains a valid
    /// stable heap.
    pub fn init(memory: M) -> Result<Self, InitError> {
        BaseVec::<T, M>::init(memory, MAGIC).map(Self)
    }

    pub fn len(&self) -> u64 {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Pushes an item onto the min heap.
    pub fn push(&mut self, item: &T) -> Result<(), GrowFailed> {
        self.0.push(item)?;
        debug_assert!(!self.is_empty());
        self.bubble_up(self.0.len().saturating_sub(1), item);
        debug_assert_eq!(Ok(()), self.check_invariant());
        Ok(())
    }

    /// Removes the smallest item from the heap and returns it.
    /// Returns `None` if the heap is empty.
    pub fn pop(&mut self) -> Option<T> {
        let n = self.len();
        match n {
            0 => None,
            1 => self.0.pop(),
            _more => {
                let smallest = self.0.get(0).unwrap();
                let last = self.0.pop().unwrap();
                self.0.set(0, &last);
                self.bubble_down(0, n, &last);
                debug_assert_eq!(Ok(()), self.check_invariant());
                Some(smallest)
            }
        }
    }

    /// Returns the smallest item in the heap.
    /// Returns `None` if the heap is empty.
    pub fn peek(&self) -> Option<T> {
        self.0.get(0)
    }

    /// Returns an iterator visiting all values in the underlying vector, in arbitrary order.
    pub fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.0.iter()
    }

    #[cfg(debug_assertions)]
    fn check_invariant(&self) -> Result<(), String> {
        let n = self.len();
        for i in (1..n).rev() {
            let p = (i - 1) / 2;
            let item = self.0.get(i).unwrap();
            let parent = self.0.get(p).unwrap();
            if parent.partial_cmp(&item) == Some(std::cmp::Ordering::Greater) {
                return Err(format!(
                    "Binary heap invariant violated in indices {i} and {p}"
                ));
            }
        }
        Ok(())
    }

    fn bubble_up(&mut self, mut i: u64, item: &T) {
        // LOOP INVARIANT: self.0.get(i) == item
        while i > 0 {
            let p = (i - 1) / 2;
            let parent = self.0.get(i).unwrap();
            if item.partial_cmp(&parent) == Some(std::cmp::Ordering::Less) {
                self.0.set(i, &parent);
                self.0.set(p, item);
            }
            i = p;
        }
    }

    fn bubble_down(&mut self, mut i: u64, n: u64, item: &T) {
        // LOOP INVARIANT: self.0.get(i) == item
        loop {
            let l = i * 2 + 1;
            if n <= l {
                return;
            }
            let child = self.0.get(l).unwrap();
            if child.partial_cmp(item) == Some(std::cmp::Ordering::Less) {
                self.0.set(i, &child);
                self.0.set(l, item);
                i = l;
                continue;
            }

            let r = l + 1;
            if n <= r {
                return;
            }
            let child = self.0.get(r).unwrap();
            if child.partial_cmp(item) == Some(std::cmp::Ordering::Less) {
                self.0.set(i, &child);
                self.0.set(r, item);
                i = r;
            }
        }
    }
}
