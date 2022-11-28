use crate::{vec::Vec as StableVec, BoundedStorable, Memory};

pub struct BinaryHeap<M, T> {
    data: StableVec<M, T>,
}

impl<M: Memory, T: Ord + BoundedStorable> BinaryHeap<M, T> {
    #[must_use]
    pub fn new(memory: M) -> BinaryHeap<M, T> {
        Self {
            data: StableVec::new(memory),
        }
    }

    #[must_use]
    pub fn new_with_sizes(memory: M, max_value_size: u64) -> Self {
        let data = StableVec::new_with_sizes(memory, max_value_size);
        Self { data }
    }

    pub fn load(memory: M) -> Self {
        Self::load_with_sizes(memory, T::MAX_SIZE as u64)
    }

    pub fn load_with_sizes(memory: M, max_value_size: u64) -> Self {
        // Read the header from memory.
        let data = StableVec::load_with_sizes(memory, max_value_size);
        data.into()
    }

    #[must_use]
    pub fn peek(&self) -> Option<T> {
        self.data.get(0)
    }

    pub fn clear(&mut self) {
        self.data.clear();
    }

    pub fn pop(&mut self) -> Option<T> {
        self.data.pop().map(|element| {
            if !self.is_empty() {
                let ret = self.data.get(0).unwrap();
                self.data.set(0, &element);
                self.sift_down_to_bottom(0);
                ret
            } else {
                element
            }
        })
    }

    pub fn push(&mut self, item: T) {
        let old_len = self.len();
        self.data.push(&item);
        self.sift_up(0, old_len);
    }

    #[must_use]
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.data.reserve(additional);
    }

    fn sift_up(&mut self, start: usize, pos: usize) -> usize {
        assert!(pos < self.len());
        // Take out the value at `pos` and create a hole.
        // SAFETY: Assert guarantees that pos < self.len()
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };

        while hole.pos() > start {
            let parent = (hole.pos() - 1) / 2;

            // SAFETY: hole.pos() > start >= 0, which means hole.pos() > 0
            //  and so hole.pos() - 1 can't underflow.
            //  This guarantees that parent < hole.pos() so
            //  it's a valid index and also != hole.pos().
            if hole.element() <= unsafe { &hole.get(parent) } {
                break;
            }

            // SAFETY: Same as above
            unsafe { hole.move_to(parent) };
        }

        hole.pos()
    }

    fn sift_down_range(&mut self, pos: usize, end: usize) {
        assert!(pos < end && end <= self.len());
        // SAFETY: Assert guarantees that pos < end <= self.len().
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };
        let mut child = 2 * hole.pos() + 1;

        // Loop invariant: child == 2 * hole.pos() + 1.
        while child <= end.saturating_sub(2) {
            // compare with the greater of the two children
            // SAFETY: child < end - 1 < self.len() and
            //  child + 1 < end <= self.len(), so they're valid indexes.
            //  child == 2 * hole.pos() + 1 != hole.pos() and
            //  child + 1 == 2 * hole.pos() + 2 != hole.pos().
            // FIXME: 2 * hole.pos() + 1 or 2 * hole.pos() + 2 could overflow
            //  if T is a ZST
            child += unsafe { hole.get(child) <= hole.get(child + 1) } as usize;

            // if we are already in order, stop.
            // SAFETY: child is now either the old child or the old child+1
            //  We already proven that both are < self.len() and != hole.pos()
            if hole.element() >= unsafe { &hole.get(child) } {
                return;
            }

            // SAFETY: same as above.
            unsafe { hole.move_to(child) };
            child = 2 * hole.pos() + 1;
        }

        // SAFETY: && short circuit, which means that in the
        //  second condition it's already true that child == end - 1 < self.len().
        if child == end - 1 && hole.element() < unsafe { &hole.get(child) } {
            // SAFETY: child is already proven to be a valid index and
            //  child == 2 * hole.pos() + 1 != hole.pos().
            unsafe { hole.move_to(child) };
        }
    }

    fn sift_down(&mut self, pos: usize) {
        assert!(pos < self.len());

        let len = self.len();
        self.sift_down_range(pos, len);
    }

    fn sift_down_to_bottom(&mut self, mut pos: usize) {
        assert!(pos < self.len());
        let end = self.len();
        let start = pos;

        // SAFETY: The caller guarantees that pos < self.len().
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };
        let mut child = 2 * hole.pos() + 1;

        // Loop invariant: child == 2 * hole.pos() + 1.
        while child <= end.saturating_sub(2) {
            // SAFETY: child < end - 1 < self.len() and
            //  child + 1 < end <= self.len(), so they're valid indexes.
            //  child == 2 * hole.pos() + 1 != hole.pos() and
            //  child + 1 == 2 * hole.pos() + 2 != hole.pos().
            // FIXME: 2 * hole.pos() + 1 or 2 * hole.pos() + 2 could overflow
            //  if T is a ZST
            child += unsafe { hole.get(child) <= hole.get(child + 1) } as usize;

            // SAFETY: Same as above
            unsafe { hole.move_to(child) };
            child = 2 * hole.pos() + 1;
        }

        if child == end - 1 {
            // SAFETY: child == end - 1 < self.len(), so it's a valid index
            //  and child == 2 * hole.pos() + 1 != hole.pos().
            unsafe { hole.move_to(child) };
        }
        pos = hole.pos();
        drop(hole);

        // SAFETY: pos is the position in the hole and was already proven
        //  to be a valid index.
        self.sift_up(start, pos);
    }

    fn rebuild(&mut self) {
        let mut n = self.len() / 2;
        while n > 0 {
            n -= 1;
            self.sift_down(n);
        }
    }
}

impl<M, T> BinaryHeap<M, T> {
    #[must_use]
    pub fn into_vec(self) -> StableVec<M, T> {
        self.into()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

struct Hole<'a, M, T>
where
    M: Memory,
    T: BoundedStorable,
{
    data: &'a mut StableVec<M, T>,
    value: T,
    pos: usize,
}

impl<'a, M, T> Hole<'a, M, T>
where
    M: Memory,
    T: BoundedStorable,
{
    /// Create a new `Hole` at index `pos`.
    ///
    /// Unsafe because pos must be within the data slice.
    #[inline]
    unsafe fn new(data: &'a mut StableVec<M, T>, pos: usize) -> Self {
        debug_assert!(pos < data.len());
        // SAFE: pos should be inside the slice
        let value = data.get_unchecked(pos);
        Hole { data, value, pos }
    }

    #[inline]
    fn pos(&self) -> usize {
        self.pos
    }

    /// Returns a reference to the element removed.
    #[inline]
    fn element(&self) -> &T {
        &self.value
    }

    /// Returns a reference to the element at `index`.
    ///
    /// Unsafe because index must be within the data slice and not equal to pos.
    #[inline]
    unsafe fn get(&self, index: usize) -> T {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());
        // Safe because caller guarantees that index < len && index != pos.
        self.data.get_unchecked(index)
    }

    /// Move hole to new location
    ///
    /// Unsafe because index must be within the data slice and not equal to pos.
    #[inline]
    unsafe fn move_to(&mut self, index: usize) {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());

        // SAFE: caller guarantees that index < len && index != pos.
        let val = self.data.get_unchecked(index);
        self.data.set(self.pos, &val);
        self.pos = index;
    }
}

impl<M, T> Drop for Hole<'_, M, T>
where
    M: Memory,
    T: BoundedStorable,
{
    #[inline]
    fn drop(&mut self) {
        // fill the hole again
        self.data.set(self.pos, &self.value);
    }
}

impl<M, T: Ord> From<StableVec<M, T>> for BinaryHeap<M, T>
where
    M: Memory,
    T: BoundedStorable,
{
    /// Converts a `Vec<T>` into a `BinaryHeap<T>`.
    ///
    /// This conversion happens in-place, and has *O*(*n*) time complexity.
    fn from(vec: StableVec<M, T>) -> BinaryHeap<M, T> {
        let mut heap = BinaryHeap { data: vec };
        heap.rebuild();
        heap
    }
}

impl<M: Memory + Clone, T: BoundedStorable + Ord, const N: usize> From<(M, [T; N])>
    for BinaryHeap<M, T>
{
    fn from(arr: (M, [T; N])) -> Self {
        Self::from(StableVec::from(arr))
    }
}

impl<M, T> From<BinaryHeap<M, T>> for StableVec<M, T> {
    /// Converts a `BinaryHeap<T>` into a `Vec<T>`.
    ///
    /// This conversion requires no data movement or allocation, and has
    /// constant time complexity.
    fn from(heap: BinaryHeap<M, T>) -> StableVec<M, T> {
        heap.data
    }
}
#[cfg(test)]
mod test {
    use super::*;
    use rand::{seq::SliceRandom, thread_rng};
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    #[test]
    pub fn test_push_pop() {
        let mem = make_memory();
        let mut heap = BinaryHeap::new(mem);

        let mut rng = thread_rng();
        let mut inputs: Vec<u32> = (0..100).collect();
        inputs.shuffle(&mut rng);

        for i in inputs {
            heap.push(i);
        }

        for i in (0..100).rev() {
            assert_eq!(heap.pop(), Some(i));
        }

        assert_eq!(heap.pop(), None);
    }

    #[test]
    pub fn test_load_from_mem() {
        let mem = make_memory();
        {
            let mut heap = BinaryHeap::from((mem.clone(), [0u32, 1u32, 2u32, 3u32, 4u32]));
            heap.push(5);
        }

        let mut heap: BinaryHeap<Rc<RefCell<Vec<u8>>>, u32> = BinaryHeap::load(mem);

        assert_eq!(heap.pop(), Some(5u32));
        assert_eq!(heap.pop(), Some(4u32));
        assert_eq!(heap.pop(), Some(3u32));
        assert_eq!(heap.pop(), Some(2u32));
        assert_eq!(heap.pop(), Some(1u32));
        assert_eq!(heap.pop(), Some(0u32));

        assert_eq!(heap.pop(), None);
    }
}
