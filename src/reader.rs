use crate::{Memory, WASM_PAGE_SIZE};
use std::io;

#[cfg(test)]
mod tests;

/// A reader to the stable memory.
///
/// Keeps an offset and reads off memory consecutively.
pub struct Reader<'a, M> {
    /// The offset of the next read.
    offset: u64,

    /// The stable memory to read data from.
    memory: &'a M,
}

#[derive(Debug)]
pub struct OutOfBounds {
    pub max_address: u64,
    pub attempted_read_address: u64,
}

impl<'a, M: Memory> Reader<'a, M> {
    /// Creates a new `Reader` which reads from the selected memory starting from the specified offset.
    pub fn new(memory: &'a M, offset: u64) -> Self {
        Self { offset, memory }
    }

    /// Reads data from the memory location specified by an offset.
    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize, OutOfBounds> {
        let memory_end_addr = self.memory.size() * WASM_PAGE_SIZE;

        let read_buf = if buf.len() as u64 + self.offset > memory_end_addr {
            if self.offset < memory_end_addr {
                // read only until the end of stable memory if an oversized buffer is provided
                let available_bytes = (memory_end_addr - self.offset) as usize;
                &mut buf[..available_bytes]
            } else {
                return Err(OutOfBounds {
                    max_address: memory_end_addr,
                    attempted_read_address: self.offset,
                });
            }
        } else {
            buf
        };

        self.memory.read(self.offset, read_buf);
        self.offset += read_buf.len() as u64;
        Ok(read_buf.len())
    }
}

impl<M: Memory> io::Read for Reader<'_, M> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Error> {
        self.read(buf).or(Ok(0)) // Read defines EOF to be success
    }
}

/// A reader to the stable memory which reads bytes a chunk at a time as each chunk is required.
pub struct BufferedReader<'a, M> {
    inner: io::BufReader<Reader<'a, M>>,
}

impl<M: Memory> BufferedReader<'_, M> {
    /// Creates a new `BufferedReader` which reads from the selected memory
    pub fn new(buffer_size: usize, reader: Reader<M>) -> BufferedReader<M> {
        BufferedReader {
            inner: io::BufReader::with_capacity(buffer_size, reader),
        }
    }
}

impl<M: Memory> io::Read for BufferedReader<'_, M> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.read(buf)
    }
}
