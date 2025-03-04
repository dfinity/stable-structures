use crate::{safe_write, GrowFailed, Memory};
use std::io;

#[cfg(test)]
mod tests;

/// A writer that writes sequentially to memory.
///
/// Warning: This will overwrite any existing data in stable memory as it writes, so ensure you set
/// the `offset` value accordingly if you wish to preserve existing data.
///
/// The writer Will attempt to grow the memory as it writes.
pub struct Writer<'a, M> {
    /// The offset of the next write.
    offset: u64,

    /// The stable memory to write data to.
    memory: &'a mut M,
}

impl<'a, M: Memory> Writer<'a, M> {
    /// Creates a new `Writer` which writes to the selected memory starting from the offset.
    pub fn new(memory: &'a mut M, offset: u64) -> Self {
        Self { offset, memory }
    }

    /// Writes a byte slice to the underlying memory directly.
    ///
    /// Note: The writer will first attempt to grow the memory enough to write _all_ the data and
    /// only then start writing. If the memory can not be grown sufficiently, the write is aborted
    /// without writing any data.
    pub fn write(&mut self, buf: &[u8]) -> Result<(), GrowFailed> {
        safe_write(self.memory, self.offset, buf)?;
        self.offset += buf.len() as u64;
        Ok(())
    }
}

impl<M: Memory> io::Write for Writer<'_, M> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, io::Error> {
        self.write(buf)
            .map_err(|e| io::Error::new(io::ErrorKind::OutOfMemory, e))?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        // Noop.
        Ok(())
    }
}

/// A writer to the stable memory which first writes the bytes to an in memory buffer and flushes
/// the buffer to stable memory each time it becomes full.
///
/// Warning: This will overwrite any existing data in stable memory as it writes, so ensure you set
/// the `offset` value accordingly if you wish to preserve existing data.
///
/// Note: Each call to grow or write to stable memory is a relatively expensive operation, so pick a
/// buffer size large enough to avoid excessive calls to stable memory.
pub struct BufferedWriter<'a, M: Memory> {
    inner: io::BufWriter<Writer<'a, M>>,
}

impl<M: Memory> BufferedWriter<'_, M> {
    /// Creates a new `BufferedStableWriter` which writes to the selected memory
    pub fn new(buffer_size: usize, writer: Writer<M>) -> BufferedWriter<M> {
        BufferedWriter {
            inner: io::BufWriter::with_capacity(buffer_size, writer),
        }
    }
}

impl<M: Memory> io::Write for BufferedWriter<'_, M> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.inner.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}
