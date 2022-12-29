use crate::{Memory, WASM_PAGE_SIZE};
use std::collections::BTreeMap;
use std::cell::RefCell;

#[derive(Clone)]
pub struct MemoryStats<M: Memory> {
    memory: M,

    // There are behind a RefCell because `read` and `write` don't take a mutable self.
    read_pages: RefCell<BTreeMap<u64, u64>>,
    dirty_pages: RefCell<BTreeMap<u64, u64>>,
}

impl<M: Memory> MemoryStats<M> {
    pub fn new(memory: M) -> Self {
        Self {
            memory,
            read_pages: RefCell::new(BTreeMap::default()),
            dirty_pages: RefCell::new(BTreeMap::default()),
        }
    }

    pub fn dirty_pages(&self) -> BTreeMap<u64, u64> {
        self.dirty_pages.borrow().clone()
    }
}

impl<M: Memory> Memory for MemoryStats<M> {
    fn size(&self) -> u64 {
        self.memory.size()
    }

    fn grow(&self, pages: u64) -> i64 {
        self.memory.grow(pages)
    }

    fn read(&self, offset: u64, dst: &mut [u8]) {
        // Add pages access to read_pages.
        let mut page = offset - (offset % WASM_PAGE_SIZE);
        while page < offset + dst.len() as u64 {
            self.read_pages
                .borrow_mut()
                .entry(page)
                .and_modify(|e| *e += 1)
                .or_insert(1);
            page += WASM_PAGE_SIZE;
        }

        self.memory.read(offset, dst)
    }

    fn write(&self, offset: u64, src: &[u8]) {
        let mut page = offset - (offset % WASM_PAGE_SIZE);
        while page < offset + src.len() as u64 {
            self.dirty_pages
                .borrow_mut()
                .entry(page)
                .and_modify(|e| *e += 1)
                .or_insert(1);
            page += WASM_PAGE_SIZE;
        }

        self.memory.write(offset, src)
    }
}

// TODO: convert these into proptests.
#[cfg(test)]
mod test {
    use super::*;
    use std::rc::Rc;

    fn make_memory() -> MemoryStats<Rc<RefCell<Vec<u8>>>> {
        MemoryStats::new(Rc::new(RefCell::new(Vec::new())))
    }

    #[test]
    fn write() {
        let page_counter = make_memory();

        let size = WASM_PAGE_SIZE as usize * 10;
        let bytes = vec![0; size];
        page_counter.grow(10);
        page_counter.write(0, &bytes);

        assert_eq!(page_counter.dirty_pages.borrow().len(), 10);
    }

    #[test]
    fn write_with_offset() {
        let page_counter = make_memory();

        let size = WASM_PAGE_SIZE as usize * 10;
        let bytes = vec![0; size];
        page_counter.grow(11);
        page_counter.write(1, &bytes);

        assert_eq!(page_counter.dirty_pages.borrow().len(), 11);
    }

    #[test]
    fn read() {
        let page_counter = make_memory();

        let size = WASM_PAGE_SIZE as usize * 10;
        let mut bytes = vec![0; size];
        page_counter.grow(10);
        page_counter.read(0, &mut bytes);

        assert_eq!(page_counter.read_pages.borrow().len(), 10);
    }

    #[test]
    fn read_with_offset() {
        let page_counter = make_memory();

        let size = WASM_PAGE_SIZE as usize * 10;
        let mut bytes = vec![0; size];
        page_counter.grow(11);
        page_counter.read(1, &mut bytes);

        assert_eq!(page_counter.read_pages.borrow().len(), 11);
    }
}
