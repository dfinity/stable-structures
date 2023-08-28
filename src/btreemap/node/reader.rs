use super::*;
use crate::btreemap::node::v2::PAGE_OVERFLOW_DATA_OFFSET;
use std::cmp::min;

#[derive(Debug)]
pub struct Segment {
    pub address: Address,
    pub length: Bytes,
}

struct NodeIterator<'a> {
    pub virtual_segment: Segment,
    pub address: Address,
    pub overflows: &'a [Address],
    pub page_size: Bytes,
}

impl Iterator for NodeIterator<'_> {
    type Item = Segment;

    fn next(&mut self) -> Option<Self::Item> {
        // The segment is empty. End iteration.
        if self.virtual_segment.length == Bytes::from(0u64) {
            return None;
        }

        // Map the virtual segment's address to a real address.
        let offset = Bytes::from(self.virtual_segment.address.get());

        let (real_address, bytes_in_segment) = if offset < self.page_size {
            // The address is in the initial page.
            let real_address = self.address + offset;

            // Compute how many bytes are in this real segment.
            let bytes_in_segment = {
                let end_page_offset = self.page_size;

                // Write up to either the end of the page, or the end of the segment.
                min(end_page_offset - offset, self.virtual_segment.length)
            };

            (real_address, bytes_in_segment)
        } else {
            // The amount of data that can be stored in an overflow page.
            let overflow_data_size = self.page_size - PAGE_OVERFLOW_DATA_OFFSET;

            // The offset is in the overflows.
            let overflow_idx =
                ((offset - self.page_size).get() as usize) / (overflow_data_size.get() as usize);

            let offset_in_overflow =
                ((offset - self.page_size).get() as usize) % (overflow_data_size.get() as usize);

            let overflow_page_end_offset =
                self.page_size + Bytes::from((overflow_idx + 1) as u64) * overflow_data_size;

            let real_address = self.overflows[overflow_idx]
                + PAGE_OVERFLOW_DATA_OFFSET
                + Bytes::new(offset_in_overflow as u64);

            // Compute how many bytes are in this real segment.
            let bytes_in_segment = {
                let end_page_offset = overflow_page_end_offset;

                // Write up to either the end of the page, or the end of the segment.
                min(end_page_offset - offset, self.virtual_segment.length)
            };

            (real_address, bytes_in_segment)
        };

        // Update the virtual segment to exclude the portion we're about to return.
        self.virtual_segment.length -= bytes_in_segment;
        self.virtual_segment.address += bytes_in_segment;

        Some(Segment {
            address: real_address,
            length: bytes_in_segment,
        })
    }
}

pub struct NodeReader<'a, M: Memory> {
    pub address: Address,
    pub overflows: Vec<Address>,
    pub page_size: PageSize,
    pub memory: &'a M,
}

impl<'a, M: Memory> Memory for NodeReader<'a, M> {
    fn size(&self) -> u64 {
        panic!("");
    }

    fn grow(&self, _: u64) -> i64 {
        panic!("");
    }

    fn read(&self, offset: u64, dst: &mut [u8]) {
        if (offset + dst.len() as u64) < self.page_size.get() as u64 {
            self.memory.read(self.address.get() + offset, dst);
            return;
        }

        let iter = NodeIterator {
            virtual_segment: Segment {
                address: Address::from(offset),
                length: Bytes::from(dst.len() as u64),
            },
            address: self.address,
            overflows: &self.overflows,
            page_size: Bytes::from(self.page_size.get()),
        };

        let mut bytes_read = 0;
        for Segment { address, length } in iter {
            self.memory.read(
                address.get(),
                &mut dst[bytes_read as usize..(bytes_read + length.get()) as usize],
            );

            bytes_read += length.get();
        }
    }

    fn write(&self, _: u64, _: &[u8]) {
        panic!("out of bounds")
    }
}
