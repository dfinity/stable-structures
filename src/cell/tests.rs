use crate::cell::Cell;
use crate::storable::Storable;
use crate::vec_mem::VectorMemory;
use crate::{Memory, RestrictedMemory, WASM_PAGE_SIZE};

fn reload<T: Default + Storable, M: Memory>(c: Cell<T, M>) -> Cell<T, M> {
    Cell::init(c.into_memory(), T::default())
}

#[test]
fn test_cell_init() {
    let mem = VectorMemory::default();
    let cell = Cell::init(mem, 1024u64);
    assert_eq!(*cell.get(), 1024u64);
    let mem = cell.into_memory();
    assert_ne!(mem.size(), 0);
    let cell = Cell::init(mem, 0u64);
    assert_eq!(1024u64, *cell.get());

    // Check that Cell::new overwrites the contents unconditionally.
    let cell = Cell::new(cell.into_memory(), 2048u64);
    assert_eq!(2048u64, *cell.get());
}

#[test]
fn test_cell_init_empty() {
    let mem = VectorMemory::default();
    let cell = Cell::init(mem, vec![]);
    assert_eq!(Vec::<u8>::new(), *cell.get());
}

#[test]
#[should_panic(expected = "ValueTooLarge { value_size: 65536 }")]
fn test_failure_out_of_space() {
    let mem = RestrictedMemory::new(VectorMemory::default(), 0..1);
    let data = [1u8; 100];
    let mut cell = Cell::new(mem, data.to_vec());

    assert_eq!(&data[..], &cell.get()[..]);

    cell.set(vec![2u8; WASM_PAGE_SIZE as usize]);
}

#[test]
fn test_cell_grow_and_shrink() {
    let mem = VectorMemory::default();
    let mut cell = Cell::init(mem, vec![1u8; 10]);

    cell.set(vec![2u8; 20]);
    let mut cell = reload(cell);
    assert_eq!(&[2u8; 20][..], &cell.get()[..]);

    cell.set(vec![3u8; 5]);
    let cell = reload(cell);
    assert_eq!(&[3u8; 5][..], &cell.get()[..]);
}

#[test]
fn can_store_unbounded_type() {
    let mem = VectorMemory::default();
    let test_string = "Another string with different content".to_string();

    let mut cell = Cell::init(mem, test_string.clone());
    assert_eq!(test_string, *cell.get());

    let new_string = "This is a test string that can be very long and unbounded".to_string();
    cell.set(new_string.clone());
    assert_eq!(new_string, *cell.get());

    // Test reloading from memory
    let cell = reload(cell);
    assert_eq!(new_string, *cell.get());
}
