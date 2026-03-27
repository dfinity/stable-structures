use crate::data_size::DataSize;

pub trait ReportMemoryUsage: DataSize {
    /// Estimates the total memory usage including heap and stack in bytes.
    fn heap_memory_usage(&self) -> usize {
        self.data_size()
    }

    /// Estimates the size of allocated stable memory in bytes.
    fn stable_memory_allocation(&self) -> usize;

    /// Estimates the actual memory usage in stable memory in bytes.
    fn stable_memory_usage(&self) -> usize;
}
