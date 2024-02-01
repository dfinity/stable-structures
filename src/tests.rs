use super::*;
use crate::memory_manager::MemoryManager;
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn test_restricted_memory_growth() {
    let base = Rc::new(RefCell::new(vec![0u8; 0]));
    let mem = RestrictedMemory::new(Rc::clone(&base), 3..10);

    assert_eq!(base.size(), 0);
    assert_eq!(mem.size(), 0);

    assert_eq!(mem.grow(1), 0);
    assert_eq!(mem.size(), 1);
    assert_eq!(base.size(), 4);

    assert_eq!(base.grow(1), 4);
    assert_eq!(base.size(), 5);
    assert_eq!(mem.size(), 2);

    assert_eq!(mem.grow(5), 2);
    assert_eq!(mem.size(), 7);
    assert_eq!(mem.grow(1), -1);
    assert_eq!(base.size(), 10);
}

#[test]
fn test_restricted_memory_rw() {
    let base = Rc::new(RefCell::new(vec![0u8; 0]));
    let mem = RestrictedMemory::new(Rc::clone(&base), 3..10);

    assert_eq!(mem.grow(1), 0);

    mem.write(10, b"DEADBEEF");
    let mut buf = [0u8; 10];
    base.read(3 * WASM_PAGE_SIZE + 10, &mut buf[0..8]);
    assert_eq!(&buf[0..8], b"DEADBEEF");

    mem.read(10, &mut buf[2..10]);
    assert_eq!(&buf[2..10], b"DEADBEEF");
}

#[test]
#[ignore]
fn vec_exposes_init_err() {
    // Ensures that the `vec` module exposes `InitError` to avoid breaking
    // clients that depend on it.
    #[allow(unused_imports)]
    use crate::vec::InitError;
}

#[test]
fn should_be_able_to_recover_memory_from_memory_manager() {
    let raw_memory = DefaultMemoryImpl::default();
    let memory_manager = MemoryManager::init(raw_memory);
    let recovered_memory = memory_manager.into_inner();
    assert!(recovered_memory.is_some());
}
