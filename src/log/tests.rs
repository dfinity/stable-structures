use crate::log::{iter_thread_local, InitError, Log, WriteError};
use crate::vec_mem::VectorMemory;
use crate::{Memory, RestrictedMemory, WASM_PAGE_SIZE};
use std::cell::RefCell;

thread_local! {
    static STRING_LOG: RefCell<Log<String, VectorMemory, VectorMemory>> = RefCell::new(new_string_log());
}

fn new_string_log() -> Log<String, VectorMemory, VectorMemory> {
    Log::init(VectorMemory::default(), VectorMemory::default())
        .expect("failed to initialize stable log")
}

#[test]
fn test_log_construct() {
    let log = Log::<Vec<u8>, _, _>::new(VectorMemory::default(), VectorMemory::default());

    assert_eq!(log.len(), 0);
    assert_eq!(log.log_size_bytes(), 0);
    assert_eq!(log.index_size_bytes(), 40);
    let (index_memory, data_memory) = log.into_memories();

    let log = Log::<Vec<u8>, _, _>::init(index_memory, data_memory).expect("failed to init log");
    assert_eq!(log.len(), 0);
    assert_eq!(log.log_size_bytes(), 0);
    assert_eq!(log.index_size_bytes(), 40);
}

#[test]
fn test_new_overwrites() {
    let log = Log::<Vec<u8>, _, _>::new(VectorMemory::default(), VectorMemory::default());
    log.append(&b"DEADBEEF".to_vec())
        .expect("failed to append entry");

    assert_eq!(log.len(), 1);

    let (index_memory, data_memory) = log.into_memories();
    let log = Log::<Vec<u8>, _, _>::new(index_memory, data_memory);
    assert_eq!(log.len(), 0);
}

#[test]
fn test_log_init_empty() {
    let log = Log::<Vec<u8>, _, _>::init(VectorMemory::default(), VectorMemory::default())
        .expect("failed to init log");

    assert_eq!(log.len(), 0);
    assert_eq!(log.log_size_bytes(), 0);
    assert_eq!(log.index_size_bytes(), 40);
}

#[test]
fn test_log_init_with_different_data_magic() {
    let mem = VectorMemory::default();
    assert_eq!(mem.grow(1), 0);
    mem.write(0, b"WAS");
    let log = Log::<Vec<u8>, _, _>::init(VectorMemory::default(), mem).expect("failed to init log");
    assert_eq!(log.len(), 0);
}

#[test]
fn test_log_init_with_different_index_magic() {
    let index_mem = VectorMemory::default();
    assert_eq!(index_mem.grow(1), 0);
    index_mem.write(0, b"WAS");
    let data_mem = VectorMemory::default();
    assert_eq!(data_mem.grow(1), 0);
    data_mem.write(0, b"GLD\x01");
    assert_eq!(
        Log::<Vec<u8>, _, _>::init(index_mem, data_mem)
            .map(|_| ())
            .unwrap_err(),
        InitError::InvalidIndex
    );
}

#[test]
fn test_log_load_bad_index_version() {
    let index_memory = VectorMemory::default();
    assert_eq!(index_memory.grow(1), 0);
    index_memory.write(0, b"GLI\x02");

    let data_memory = VectorMemory::default();
    assert_eq!(data_memory.grow(1), 0);
    data_memory.write(0, b"GLD\x01");
    assert_eq!(
        Log::<Vec<u8>, _, _>::init(index_memory, data_memory)
            .map(|_| ())
            .unwrap_err(),
        InitError::IncompatibleIndexVersion {
            last_supported_version: 1,
            decoded_version: 2
        },
    );
}

#[test]
fn test_log_load_bad_data_version() {
    let mem = VectorMemory::default();
    assert_eq!(mem.grow(1), 0);
    mem.write(0, b"GLD\x02");

    assert_eq!(
        Log::<Vec<u8>, _, _>::init(VectorMemory::default(), mem)
            .map(|_| ())
            .unwrap_err(),
        InitError::IncompatibleDataVersion {
            last_supported_version: 1,
            decoded_version: 2
        },
    );
}

#[test]
fn test_log_append() {
    let log = Log::<Vec<u8>, _, _>::new(VectorMemory::default(), VectorMemory::default());
    let idx1 = log
        .append(&b"DEADBEEF".to_vec())
        .expect("failed to append entry");
    let idx2 = log
        .append(&b"FEEDBAD".to_vec())
        .expect("failed to append entry");

    assert_eq!(idx1, 0);
    assert_eq!(idx2, 1);
    assert_eq!(log.len(), 2);
    assert_eq!(log.get(idx1).unwrap(), b"DEADBEEF".to_vec());
    assert_eq!(log.get(idx2).unwrap(), b"FEEDBAD".to_vec());
}

#[test]
fn test_log_append_persistence() {
    let log = Log::<Vec<u8>, _, _>::new(VectorMemory::default(), VectorMemory::default());
    let idx = log
        .append(&b"DEADBEEF".to_vec())
        .expect("failed to append entry");

    let (index_memory, data_memory) = log.into_memories();

    let log = Log::<Vec<u8>, _, _>::init(index_memory, data_memory).unwrap();
    assert_eq!(log.len(), 1);
    assert_eq!(log.get(idx).unwrap(), b"DEADBEEF".to_vec());
    assert_eq!(log.log_size_bytes(), b"DEADBEEF".len() as u64);
    assert_eq!(log.index_size_bytes(), 48); // header (32) + num entries (8) + 1 index entry (8)
    assert_eq!(log.data_size_bytes(), 40); // header (32) + 1 entry (8)
    assert_eq!(log.get(5), None);
    assert_eq!(log.get(u64::MAX), None);
}

#[test]
fn test_append_data_out_of_memory() {
    let log = Log::<Vec<u8>, _, _>::new(
        VectorMemory::default(),
        RestrictedMemory::new(VectorMemory::default(), 0..1),
    );

    assert_eq!(
        Ok(0),
        log.append(&b"small entry that fits into one page".to_vec())
    );
    assert_eq!(Ok(1), log.append(&b"another small entry".to_vec()));
    assert_eq!(
        Err(WriteError::GrowFailed {
            current_size: 1,
            delta: 1
        }),
        log.append(&[1; WASM_PAGE_SIZE as usize].to_vec())
    );
    assert_eq!(2, log.len());
}

#[test]
fn test_append_index_out_of_memory() {
    let log = Log::<Vec<u8>, _, _>::new(
        RestrictedMemory::new(VectorMemory::default(), 0..1),
        VectorMemory::default(),
    );

    for _ in 0..8_187 {
        log.append(&b"log".to_vec())
            .expect("failed to append entry");
    }
    assert_eq!(
        Err(WriteError::GrowFailed {
            current_size: 1,
            delta: 1
        }),
        log.append(&b"log".to_vec())
    );
    assert_eq!(8_187, log.len());
}

#[test]
fn test_index_grow() {
    let log = Log::<Vec<u8>, _, _>::new(VectorMemory::default(), VectorMemory::default());
    for _ in 0..8_188 {
        log.append(&b"log".to_vec())
            .expect("failed to append entry");
    }
    assert_eq!(log.index_size_bytes(), 65_544); // more than WASM_PAGE_SIZE
    let (index_memory, _) = log.into_memories();
    assert_eq!(index_memory.size(), 2)
}

#[allow(clippy::iter_nth_zero)]
#[test]
fn test_iter() {
    let log = Log::<String, _, _>::new(VectorMemory::default(), VectorMemory::default());
    assert_eq!(log.iter().next(), None);
    log.append(&"apple".to_string()).unwrap();
    log.append(&"banana".to_string()).unwrap();
    log.append(&"cider".to_string()).unwrap();

    let mut iter = log.iter();
    assert_eq!(iter.size_hint(), (3, None));
    assert_eq!(iter.next(), Some("apple".to_string()));
    assert_eq!(iter.size_hint(), (2, None));
    assert_eq!(iter.next(), Some("banana".to_string()));
    assert_eq!(iter.size_hint(), (1, None));
    assert_eq!(iter.next(), Some("cider".to_string()));
    assert_eq!(iter.size_hint(), (0, None));
    assert_eq!(iter.next(), None);

    assert_eq!(log.iter().nth(0), Some("apple".to_string()));
    assert_eq!(log.iter().nth(1), Some("banana".to_string()));
    assert_eq!(log.iter().nth(2), Some("cider".to_string()));
    assert_eq!(log.iter().nth(3), None);
    assert_eq!(log.iter().nth(4), None);
    assert_eq!(log.iter().nth(usize::MAX), None);

    assert_eq!(log.iter().count(), 3);
    assert_eq!(log.iter().count(), 3);
    assert_eq!(log.iter().skip(1).count(), 2);
    assert_eq!(log.iter().skip(2).count(), 1);
    assert_eq!(log.iter().skip(3).count(), 0);
    assert_eq!(log.iter().skip(4).count(), 0);
    assert_eq!(log.iter().skip(usize::MAX).count(), 0);
}

#[allow(clippy::iter_nth_zero)]
#[test]
fn test_thread_local_iter() {
    let new_iter = || iter_thread_local(&STRING_LOG);

    assert_eq!(new_iter().next(), None);

    STRING_LOG.with(|cell| {
        *cell.borrow_mut() = new_string_log();
        let log = cell.borrow();
        log.append(&"apple".to_string()).unwrap();
        log.append(&"banana".to_string()).unwrap();
        log.append(&"cider".to_string()).unwrap();
    });

    let mut iter = new_iter();
    assert_eq!(iter.size_hint(), (3, None));
    assert_eq!(iter.next(), Some("apple".to_string()));
    assert_eq!(iter.size_hint(), (2, None));
    assert_eq!(iter.next(), Some("banana".to_string()));
    assert_eq!(iter.size_hint(), (1, None));
    assert_eq!(iter.next(), Some("cider".to_string()));
    assert_eq!(iter.size_hint(), (0, None));
    assert_eq!(iter.next(), None);

    assert_eq!(new_iter().nth(0), Some("apple".to_string()));
    assert_eq!(new_iter().nth(1), Some("banana".to_string()));
    assert_eq!(new_iter().nth(2), Some("cider".to_string()));
    assert_eq!(new_iter().nth(3), None);
    assert_eq!(new_iter().nth(4), None);
    assert_eq!(new_iter().nth(usize::MAX), None);

    assert_eq!(new_iter().count(), 3);
    assert_eq!(new_iter().count(), 3);
    assert_eq!(new_iter().skip(1).count(), 2);
    assert_eq!(new_iter().skip(2).count(), 1);
    assert_eq!(new_iter().skip(3).count(), 0);
    assert_eq!(new_iter().skip(4).count(), 0);
    assert_eq!(new_iter().skip(usize::MAX).count(), 0);
}
