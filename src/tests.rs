use super::*;
use crate::memory_manager::{MemoryId, MemoryManager};
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
    let recovered_memory = memory_manager.into_memory();
    assert!(recovered_memory.is_some());
}

#[test]
fn should_fail_to_recover_memory_from_memory_manager_if_memory_is_in_use() {
    let raw_memory = DefaultMemoryImpl::default();
    let memory_manager = MemoryManager::init(raw_memory);
    let _a_virtual_memory = memory_manager.get(MemoryId::new(0));
    let recovered_memory = memory_manager.into_memory();
    assert!(recovered_memory.is_none());
}

#[test]
fn test_read_to_vec_roundtrip() {
    let memory = DefaultMemoryImpl::default();
    memory.grow(1);
    memory.write(0, &[5, 6, 7, 8, 9]);

    let mut out = vec![];
    read_to_vec(&memory, Address::from(0), &mut out, 5);
    assert_eq!(out, vec![5, 6, 7, 8, 9]);
}

#[test]
fn test_read_write_struct_roundtrip() {
    #[derive(Eq, PartialEq, Debug)]
    struct Foo {
        a: i32,
        b: [char; 5],
    }

    let foo = Foo {
        a: 42,
        b: ['a', 'b', 'c', 'd', 'e'],
    };

    let memory = DefaultMemoryImpl::default();
    memory.grow(1);
    write_struct(&foo, Address::from(3), &memory);

    assert_eq!(
        read_struct::<Foo, DefaultMemoryImpl>(Address::from(3), &memory),
        foo
    )
}

#[test]
fn test_vector_memory_read() {
    let memory = VectorMemory::default();
    memory.grow(1);
    memory.write(1, &[4, 6, 8]);

    {
        let mut buffer = [0; 3];
        memory.read(1, &mut buffer[..]);
        assert_eq!(buffer, [4, 6, 8]);
    }

    {
        let mut buffer = std::vec::Vec::with_capacity(3);
        unsafe {
            let ptr = buffer.as_mut_ptr();
            memory.read_unsafe(1, buffer.as_mut_ptr(), 3);
            assert_eq!(std::ptr::read(ptr), 4);
            assert_eq!(std::ptr::read(ptr.add(1)), 6);
            assert_eq!(std::ptr::read(ptr.add(2)), 8);
        }
    }
}
