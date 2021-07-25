use crate::log::*;
use crate::Memory;
use std::cell::RefCell;
use std::rc::Rc;

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

#[test]
fn test_log_construct() {
    let mem = make_memory();
    let log = StableLog::new(mem.clone(), 5).expect("failed to create log");

    assert_eq!(log.len(), 0);
    assert_eq!(log.max_len(), 5);

    std::mem::drop(log);

    let log = StableLog::load(mem).expect("failed to load log");
    assert_eq!(log.len(), 0);
    assert_eq!(log.max_len(), 5);
}

#[test]
fn test_log_load_empty() {
    match StableLog::load(make_memory()) {
        Ok(_) => panic!("unexpectedly succeeded to load log"),
        Err(e) => assert_eq!(e, LoadError::MemoryEmpty),
    }
}

#[test]
fn test_log_load_bad_magic() {
    let mem = make_memory();
    assert_eq!(mem.grow(1), 0);
    match StableLog::load(mem) {
        Ok(_) => panic!("unexpectedly succeeded to load log"),
        Err(e) => assert_eq!(e, LoadError::BadMagic([0; 3])),
    }
}

#[test]
fn test_log_load_bad_version() {
    let mem = make_memory();
    assert_eq!(mem.grow(1), 0);
    mem.write(0, b"LOG\x02");

    match StableLog::load(mem) {
        Ok(_) => panic!("unexpectedly succeeded to load log"),
        Err(e) => assert_eq!(e, LoadError::UnsupportedVersion(2)),
    }
}

#[test]
fn test_log_append() {
    let log = StableLog::new(make_memory(), 5).expect("failed to create log");
    let idx = log
        .append_entry(b"DEADBEEF")
        .expect("failed to append entry");

    assert_eq!(idx, 0);
    assert_eq!(log.len(), 1);
    assert_eq!(log.entry_meta(idx).unwrap(), (0, 8));
    assert_eq!(log.get_entry(idx).unwrap(), b"DEADBEEF".to_vec());
}

#[test]
fn test_log_append_persistence() {
    let mem = make_memory();
    let log = StableLog::new(mem.clone(), 5).expect("failed to create log");
    let idx = log
        .append_entry(b"DEADBEEF")
        .expect("failed to append entry");

    std::mem::drop(log);

    let log = StableLog::load(mem).unwrap();
    assert_eq!(log.len(), 1);
    assert_eq!(log.get_entry(idx).unwrap(), b"DEADBEEF".to_vec());
}

#[test]
fn test_log_append_limit() {
    let log = StableLog::new(make_memory(), 5).expect("failed to create log");

    for i in 0..5 {
        assert_eq!(i, log.append_entry(b"x").unwrap());
        assert_eq!(log.len() as u32, i + 1);
    }

    match log.append_entry(b"x") {
        Ok(_) => panic!("unexpectedly succeeded to append to a log"),
        Err(e) => assert_eq!(e, WriteError::IndexFull(5)),
    }
}
