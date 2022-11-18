use crate::{Memory, WASM_PAGE_SIZE};
use std::cell::RefCell;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::rc::Rc;

/// A `Memory` backed by a file.
#[derive(Clone)]
pub struct FileMemory(Rc<RefCell<File>>);

impl FileMemory {
    pub fn new(file: File) -> Self {
        Self(Rc::new(RefCell::new(file)))
    }
}

impl Memory for FileMemory {
    fn size(&self) -> u64 {
        let len = self.0.borrow().metadata().unwrap().len();
        assert_eq!(
            len % WASM_PAGE_SIZE,
            0,
            "File size must correspond to exact page sizes"
        );
        len / WASM_PAGE_SIZE
    }

    fn grow(&self, pages: u64) -> i64 {
        let previous_size = self.size();
        self.0
            .borrow()
            .set_len((previous_size + pages) * WASM_PAGE_SIZE)
            .expect("grow must succeed");
        assert_eq!(self.size(), previous_size + pages);
        previous_size as i64
    }

    fn read(&self, offset: u64, dst: &mut [u8]) {
        self.0
            .borrow_mut()
            .seek(SeekFrom::Start(offset))
            .expect("out of bounds");
        let bytes_read = self.0.borrow_mut().read(dst).expect("out of bounds");
        assert_eq!(bytes_read, dst.len(), "out of bounds");
    }

    fn write(&self, offset: u64, src: &[u8]) {
        self.0
            .borrow_mut()
            .seek(SeekFrom::Start(offset))
            .expect("out of bounds");
        let bytes_written = self.0.borrow_mut().write(src).expect("out of bounds");
        assert_eq!(bytes_written, src.len(), "out of bounds");
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::write;
    use proptest::prelude::*;

    fn make_vec_memory() -> Rc<RefCell<Vec<u8>>> {
        Rc::new(RefCell::new(Vec::new()))
    }

    fn make_file_memory() -> FileMemory {
        FileMemory::new(tempfile::tempfile().unwrap())
    }

    #[test]
    fn write_and_read_random_bytes() {
        let vec_mem = make_vec_memory();
        let file_mem = make_file_memory();

        proptest!(|(
            data in proptest::collection::vec(0..u8::MAX, 0..2*WASM_PAGE_SIZE as usize),
            offset in 0..10*WASM_PAGE_SIZE
        )| {
            // Write a random blob into the memory, growing the memory as it needs to.
            write(&file_mem, offset, &data);

            // Verify the blob can be read back.
            let mut bytes = vec![0; data.len()];
            file_mem.read(offset, &mut bytes);
            assert_eq!(bytes, data);

            // Do the same write to vec mem and verify both memories are identical.
            write(&vec_mem, offset, &data);
            assert_eq!(vec_mem.size(), file_mem.size());
            let mut buf = vec![0; (file_mem.size() * WASM_PAGE_SIZE) as usize];
            file_mem.read(0, &mut buf);
            assert_eq!(buf.as_slice(), vec_mem.borrow().as_slice());
        });
    }
}
