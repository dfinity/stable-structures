use std::cell::RefCell;
use std::collections::BTreeMap;

thread_local! {
    static STATS: RefCell<BTreeMap<&'static str, Stats>> = const { RefCell::new(BTreeMap::new()) };
}

pub struct InstructionCounter {
    name: &'static str,
}

#[derive(Clone, Copy)]
pub struct Stats {
    start_instructions: Option<u64>,
    running_count: u64,
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
        let now = instruction_count();
        STATS.with(|c| {
            let mut stats = c.borrow_mut();
            let entry = stats.entry(name).or_insert(Stats {
                start_instructions: Some(now),
                running_count: 0,
                total_instructions: 0,
                call_count: 0,
            });
            if entry.running_count == 0 {
                entry.start_instructions = Some(now);
            }
            entry.running_count += 1;
        });
        Self { name }
    }
}

impl Drop for InstructionCounter {
    fn drop(&mut self) {
        STATS.with(|c| {
            let now = instruction_count();
            let mut stats = c.borrow_mut();
            let entry = stats.entry(self.name).or_insert_with(|| {
                panic!("InstructionCounter not initialized");
            });
            entry.running_count -= 1;
            if entry.running_count == 0 {
                let elapsed = now
                    - entry
                        .start_instructions
                        .expect("start_instructions is None");
                entry.start_instructions = None;
                entry.total_instructions += elapsed;
            }
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

/*

get_helper:
total_instructions : 1157246368,
call_count         : 48674

load_node:
total_instructions : 878538985,
call_count         : 48674

search:
total_instructions : 83613904,
call_count         : 48674

into_entry:
total_instructions : 26999452,
call_count         : 10000

===
get_helper:
total_instructions : 1152818806,
call_count         : 10000

load_node:
total_instructions : 903703200,
call_count         : 48674

search:
total_instructions : 108924141,
call_count         : 48674

into_entry:
total_instructions : 31619452,
call_count         : 10000

===
get_helper:
total_instructions : 3605853485,
call_count         : 48674

load_node:
total_instructions : 853224120,
call_count         : 48674

search:
total_instructions : 58137654,
call_count         : 48674

into_entry:
total_instructions : 22348944,
call_count         : 10000

===
*/
