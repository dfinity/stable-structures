use super::*;
use crate::btreemap::node::v2::PAGE_OVERFLOW_DATA_OFFSET;
use std::cmp::min;

/// A `NodeReader` abstracts the `Node` as a single contiguous memory, even though internally
/// it can be composed of multiple pages.
pub struct NodeReader<'a, M: Memory> {
    pub address: Address,
    pub overflows: &'a [Address],
    pub page_size: PageSize,
    pub memory: &'a M,
}

// Note: The `Memory` interface is implemented so that helper methods such `read_u32`,
// `read_struct`, etc. can be used with a `NodeReader` directly.
impl<'a, M: Memory> Memory for NodeReader<'a, M> {
    fn read(&self, offset: u64, dst: &mut [u8]) {
        // If the read is only in the initial page, then read it directly in one go.
        // This is a performance enhancement to avoid the cost of creating a `NodeIterator`.
        if (offset + dst.len() as u64) < self.page_size.get() as u64 {
            self.memory.read(self.address.get() + offset, dst);
            return;
        }

        // The read is split across several pages. Create a `NodeIterator` to to read from
        // each of the individual pages.
        let iter = NodeIterator::new(
            VirtualSegment {
                address: Address::from(offset),
                length: Bytes::from(dst.len() as u64),
            },
            Bytes::from(self.page_size.get()),
        );

        let mut bytes_read = 0;
        for RealSegment {
            page_idx,
            offset,
            length,
        } in iter
        {
            if page_idx == 0 {
                self.memory.read(
                    (self.address + offset).get(),
                    &mut dst[bytes_read as usize..(bytes_read + length.get()) as usize],
                );
            } else {
                self.memory.read(
                    (self.overflows[page_idx - 1] + offset).get(),
                    &mut dst[bytes_read as usize..(bytes_read + length.get()) as usize],
                );
            }

            bytes_read += length.get();
        }
    }

    fn write(&self, _: u64, _: &[u8]) {
        unreachable!("NodeReader does not support write")
    }

    fn size(&self) -> u64 {
        unreachable!("NodeReader does not support size")
    }

    fn grow(&self, _: u64) -> i64 {
        unreachable!("NodeReader does not support grow")
    }
}

#[derive(Debug)]
struct VirtualSegment {
    address: Address,
    length: Bytes,
}

struct RealSegment {
    page_idx: usize,
    offset: Bytes,
    length: Bytes,
}

// An iterator that maps a segment of a node into segments of its underlying memory.
//
// A segment in a node can map to multiple segments of memory. Here's an example:
//
// Node
// --------------------------------------------------------
//          (A) ---------- SEGMENT ---------- (B)
// --------------------------------------------------------
// ↑               ↑               ↑               ↑
// Page 0        Page 1          Page 2          Page 3
//
// The [`Node`] is internally divided into fixed-size pages. In the node's virtual address space,
// all these pages are consecutive, but in the underlying memory this may not be the case.
//
// A virtual segment would be split at the page boundaries. The example virtual segment
// above would be split into the following "real" segments:
//
//    (A, end of page 0)
//    (start of page 1, end of page 1)
//    (start of page 2, B)
//
// Each of the segments above can then be translated into the real address space by looking up
// the pages' addresses in the underlying memory.
struct NodeIterator {
    virtual_segment: VirtualSegment,
    page_size: Bytes,

    // The amount of data that can be stored in an overflow page.
    overflow_page_capacity: Bytes,
}

impl NodeIterator {
    #[inline]
    fn new(virtual_segment: VirtualSegment, page_size: Bytes) -> Self {
        Self {
            virtual_segment,
            page_size,
            overflow_page_capacity: page_size - PAGE_OVERFLOW_DATA_OFFSET,
        }
    }
}

impl Iterator for NodeIterator {
    type Item = RealSegment;

    fn next(&mut self) -> Option<Self::Item> {
        // The segment is empty. End iteration.
        if self.virtual_segment.length == Bytes::from(0u64) {
            return None;
        }

        let offset = Bytes::from(self.virtual_segment.address.get());

        // Compute the page where the segment begins.
        let page_idx = if offset < self.page_size {
            0 // The segment begins in the initial page.
        } else {
            // The segment begins in an overflow page.
            ((offset - self.page_size) / self.overflow_page_capacity).get() + 1
        };

        // Compute the length of the next real segment.
        // The length of the real segment is either up to the end of the page, or the end of the
        // virtual segment, whichever is smaller.
        let length = {
            let page_end = self.page_size + self.overflow_page_capacity * page_idx;
            min(page_end - offset, self.virtual_segment.length)
        };

        // Compute the offset within the page.
        let offset = if offset < self.page_size {
            offset
        } else {
            // The offset is in the overflow pages.
            PAGE_OVERFLOW_DATA_OFFSET + (offset - self.page_size) % self.overflow_page_capacity
        };

        // Update the virtual segment to exclude the portion we're about to return.
        self.virtual_segment.length -= length;
        self.virtual_segment.address += length;

        Some(RealSegment {
            page_idx: page_idx as usize,
            offset,
            length,
        })
    }
}
