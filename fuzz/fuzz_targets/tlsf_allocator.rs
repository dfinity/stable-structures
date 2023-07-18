#![no_main]
use ic_stable_structures::{tlsf::TlsfAllocator, types::Address, Memory};
use libfuzzer_sys::arbitrary;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

#[derive(Arbitrary, Debug)]
enum AllocatorMethod {
    Allocate {
        // The size of allocation to make.
        data: Vec<u8>,
    },
    Free {
        // Free the index^th allocation we've made.
        index: usize,
    },
}

fn make_memory() -> Rc<RefCell<Vec<u8>>> {
    Rc::new(RefCell::new(Vec::new()))
}

fuzz_target!(|methods: Vec<AllocatorMethod>| {
    println!("Methods: {:?}", methods.len());
    let mem = make_memory();
    let mut allocator = TlsfAllocator::new(mem.clone(), Address::from(0));

    let mut allocations = BTreeMap::new();

    for method in methods.into_iter() {
        match method {
            AllocatorMethod::Allocate { data } => {
                assert!(data.len() <= u32::MAX as usize);

                // Allocate memory.
                let address = allocator.allocate(data.len() as u32);
                mem.write(address.get(), &data);
                allocations.insert(address, data);
            }
            AllocatorMethod::Free { index } => {
                if let Some((address, expected_data)) = allocations.iter().nth(index) {
                    let mut actual_data = vec![0; expected_data.len()];
                    mem.read(address.get(), &mut actual_data);
                    assert_eq!(actual_data.as_slice(), expected_data);
                }
            }
        }
    }

    // Free any remaining allocations.
    for (address, expected_data) in allocations.into_iter() {
        let mut actual_data = vec![0; expected_data.len()];
        mem.read(address.get(), &mut actual_data);
        assert_eq!(actual_data.as_slice(), expected_data);
    }
});
