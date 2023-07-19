use super::*;
use proptest::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;
use tiny_rng::{Rand, Rng};

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

#[test]
fn allocate() {
    let mem = make_memory();
    let mut tlsf = TlsfAllocator::new(mem, Address::from(0));
    let block_1 = tlsf.allocate(1232);

    let block_2 = tlsf.allocate(45);

    let block_3 = tlsf.allocate(39);

    assert_eq!(
        tlsf.free_lists
            .get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
        tlsf.data_offset()
            + Bytes::from(1232u64)
            + Bytes::from(UsedBlock::header_size())
            + Bytes::from(45u64)
            + Bytes::from(UsedBlock::header_size())
            + Bytes::from(39u64)
            + Bytes::from(UsedBlock::header_size())
    );

    tlsf.deallocate(block_3);

    assert_eq!(
        tlsf.free_lists
            .get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
        tlsf.data_offset()
            + Bytes::from(1232u64)
            + Bytes::from(UsedBlock::header_size())
            + Bytes::from(45u64)
            + Bytes::from(UsedBlock::header_size())
    );

    tlsf.deallocate(block_2);

    assert_eq!(
        tlsf.free_lists
            .get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
        tlsf.data_offset() + Bytes::from(1232u64) + Bytes::from(UsedBlock::header_size())
    );

    tlsf.deallocate(block_1);

    assert_eq!(
        tlsf.free_lists
            .get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
        tlsf.data_offset()
    );
}

#[test]
fn new_and_load() {
    let mem = make_memory();
    let allocator_addr = Address::from(16);

    // Create a new allocator.
    TlsfAllocator::new(mem.clone(), allocator_addr);

    // Load it from memory.
    let tlsf = TlsfAllocator::load(mem, allocator_addr);

    // Load the first memory chunk.
    assert_eq!(
        FreeBlock::load(tlsf.data_offset(), &tlsf.memory),
        FreeBlock::genesis(tlsf.data_offset())
    );
}

// TODO: maybe make this test explicit on the "search_suitable_block"
#[test]
fn reallocate_a_block() {
    let mem = make_memory();
    let allocator_addr = Address::from(16);

    // Create a new allocator.
    let mut allocator = TlsfAllocator::new(mem, allocator_addr);

    // Make two allocations.
    // Blocks will look like this: | a (10) | b (10) | <free space>
    let a = allocator.allocate(10);
    let b = allocator.allocate(10);

    // Remove block a
    // | free (10) | b (10) | <free space>
    allocator.deallocate(a);

    // Allocate the same block again.
    allocator.allocate(10);
}

#[test]
fn reloading_preserves_allocations() {
    let mem = make_memory();
    let allocator_addr = Address::from(16);

    // Create a new allocator.
    let mut allocator = TlsfAllocator::new(mem.clone(), allocator_addr);

    let a = allocator.allocate(123);

    let mut allocator = TlsfAllocator::load(mem, allocator_addr);

    // `a` can still be deallocated.
    allocator.deallocate(a);
}

// TODO: add tests with small memory pools

#[test]
fn allocate_then_deallocate_randomly() {
    proptest!(|(
        data in proptest::collection::vec(
            proptest::collection::vec(0..u8::MAX, 3usize..100usize), 3..100
        ),
    )| {
        let mut rng = Rng::from_seed(0);
        let mem = make_memory();
        let mut tlsf = TlsfAllocator::new(mem, Address::from(0));
        let mut addresses: Vec<(Address, Vec<u8>)> = vec![];

        for d in data.into_iter() {
            let address = tlsf.allocate(d.len() as u32);

            // Write the data into memory.
            tlsf.memory.write(address.get(), &d);

            addresses.push((address, d));
        }

        // Shuffle addresses to deallocate them in random order.
        rng.shuffle(&mut addresses);
        for (address, data) in addresses {
            // Read data from memory and verify its there.
            let mut v = vec![0; data.len()];
            tlsf.memory.read(address.get(), &mut v);
            assert_eq!(v, data);

            tlsf.deallocate(address);
        }

        prop_assert_eq!(
            FreeBlock::load(tlsf.data_offset(), &tlsf.memory),
            FreeBlock::genesis(tlsf.data_offset())
        );

        prop_assert_eq!(
            tlsf.free_lists,
            TlsfAllocator::new(make_memory(), Address::from(0)).free_lists
        );
    });
}

#[test]
fn multiple_allocations_no_deallocations() {
    proptest!(|(
        data in proptest::collection::vec(
            proptest::collection::vec(0..u8::MAX, 32usize..100usize), 1..100
        ),
    )| {
        let mem = make_memory();
        let mut tlsf = TlsfAllocator::new(mem, Address::from(0));
        let mut addresses: Vec<(Address, Vec<u8>)> = vec![];

        let mut offset = Bytes::new(0);
        for d in data.into_iter() {
            let address = tlsf.allocate(d.len() as u32);

            // Asserts that the free lists have been updated accordingly.
            offset += Bytes::from(UsedBlock::header_size()) + Bytes::from(d.len() as u64);
            prop_assert_eq!(
                tlsf.free_lists.get(FIRST_LEVEL_INDEX_SIZE - 1, SECOND_LEVEL_INDEX_SIZE - 1),
                tlsf.data_offset() + offset
            );

            // Write the data into memory.
            tlsf.memory.write(address.get(), &d);
            addresses.push((address, d));
        }

        // Read all the data from memory.
        let mut v = Vec::new();
        for (address, data) in addresses {
            v.resize(data.len(), 0);
            // Read data from memory and verify its there.
            tlsf.memory.read(address.get(), &mut v);
            prop_assert_eq!(&v, &data);
        }
    });
}
