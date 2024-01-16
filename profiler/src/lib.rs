//! A module for profiling canisters.
#[cfg(feature = "benchmark")]
pub mod benchmark;

use std::cell::RefCell;
use std::collections::BTreeMap;

thread_local! {
    static PROFILING: RefCell<BTreeMap<&'static str, u64>> = RefCell::new(BTreeMap::new());
}

/// Starts profiling the instructions consumed.
///
/// Instructions are counted and recorded under the given name until the
/// `Profile` object returned is dropped.
pub fn profile(name: &'static str) -> Profile {
    Profile::new(name)
}

/// Clears all profiling data.
pub fn reset() {
    PROFILING.with(|p| p.borrow_mut().clear());
}

/// Returns the number of instructions used for each of the profile names.
pub fn get_results() -> std::collections::BTreeMap<&'static str, u64> {
    PROFILING.with(|p| p.borrow().clone())
}

pub struct Profile {
    name: &'static str,
    start_instructions: u64,
}

impl Profile {
    fn new(name: &'static str) -> Self {
        Self {
            name,
            start_instructions: instruction_count(),
        }
    }
}

impl Drop for Profile {
    fn drop(&mut self) {
        let instructions_count = instruction_count() - self.start_instructions;

        PROFILING.with(|p| {
            let mut p = p.borrow_mut();
            let entry = p.entry(self.name).or_insert(0);
            *entry += instructions_count;
        });
    }
}

fn instruction_count() -> u64 {
    #[cfg(target_arch = "wasm32")]
    {
        ic_cdk::api::performance_counter(0)
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        // Consider using cpu time here.
        0
    }
}
