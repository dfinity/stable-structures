use crate::mem_size::MemSize;

pub trait ReportMemoryUsage: MemSize {
    /// Estimates the total memory usage including heap and stack in bytes.
    fn heap_memory_usage(&self) -> usize {
        self.mem_size()
    }

    /// Estimates the size of allocated stable memory in bytes.
    fn stable_memory_allocation(&self) -> usize;

    /// Estimates the actual memory usage in stable memory in bytes.
    fn stable_memory_usage(&self) -> usize;
}
