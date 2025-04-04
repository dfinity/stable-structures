use std::cell::RefCell;
use std::collections::BTreeMap;

thread_local! {
    static STATS: RefCell<BTreeMap<&'static str, Stats>> = const { RefCell::new(BTreeMap::new()) };
}

pub struct InstructionCounter {
    name: &'static str,
    start_instructions: u64,
}

#[derive(Clone, Copy)]
pub struct Stats {
    total_instructions: u64,
    call_count: u64,
}

impl std::fmt::Debug for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Stats: ")?;
        writeln!(f, "total_instructions : {}, ", self.total_instructions)?;
        writeln!(f, "call_count         : {}", self.call_count)?;
        Ok(())
    }
}

impl InstructionCounter {
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            start_instructions: instruction_count(),
        }
    }
}

impl Drop for InstructionCounter {
    fn drop(&mut self) {
        let elapsed = instruction_count() - self.start_instructions;
        STATS.with(|c| {
            let mut stats = c.borrow_mut();
            let entry = stats.entry(self.name).or_insert(Stats {
                total_instructions: 0,
                call_count: 0,
            });
            entry.total_instructions += elapsed;
            entry.call_count += 1;
        });
    }
}

pub fn get_stats() -> Vec<(&'static str, Stats)> {
    STATS.with(|c| {
        let stats = c.borrow();
        let mut stats_vec: Vec<_> = stats.iter().map(|(&k, &v)| (k, v)).collect();
        stats_vec.sort_by(|a, b| b.1.total_instructions.cmp(&a.1.total_instructions));
        stats_vec
    })
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

pub fn print(msg: String) {
    #[cfg(target_arch = "wasm32")]
    {
        ic_cdk::api::print(msg);
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        println!("{msg}");
    }
}
