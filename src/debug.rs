use std::cell::RefCell;
use std::collections::LinkedList;

thread_local! {
    static ENTRIES: RefCell<LinkedList<Measurement>> = const { RefCell::new(LinkedList::new()) };
}

struct Measurement {
    name: &'static str,
    time: u64,
    is_start: bool,
}

pub struct InstructionCounter {
    name: &'static str,
}

impl InstructionCounter {
    pub fn new(name: &'static str) -> Self {
        let time = instruction_count();
        ENTRIES.with(|c| {
            c.borrow_mut().push_back(Measurement {
                name,
                time,
                is_start: true,
            });
        });
        Self { name }
    }
}

impl Drop for InstructionCounter {
    fn drop(&mut self) {
        let time = instruction_count();
        ENTRIES.with(|c| {
            c.borrow_mut().push_back(Measurement {
                name: self.name,
                time,
                is_start: false,
            });
        });
    }
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

pub fn get_stats() -> Vec<(&'static str, Stats)> {
    let start = instruction_count();
    let mut stats = std::collections::HashMap::new();
    ENTRIES.with(|c| {
        for measurement in c.borrow().iter() {
            let entry = stats.entry(measurement.name).or_insert(Stats {
                start_instructions: None,
                running_count: 0,
                total_instructions: 0,
                call_count: 0,
            });
            if measurement.is_start {
                entry.call_count += 1;
                if entry.running_count == 0 {
                    entry.start_instructions = Some(measurement.time);
                }
                entry.running_count += 1;
            } else {
                entry.running_count -= 1;
                if entry.running_count == 0 {
                    let instructions = measurement.time - entry.start_instructions.unwrap();
                    entry.total_instructions += instructions;
                }
            }
        }
    });

    let mut stats_vec: Vec<_> = stats.iter().map(|(&k, &v)| (k, v)).collect();
    stats_vec.sort_by(|a, b| b.1.total_instructions.cmp(&a.1.total_instructions));

    stats_vec.push((
        "get_stats",
        Stats {
            start_instructions: None,
            running_count: 0,
            total_instructions: instruction_count() - start,
            call_count: 1,
        },
    ));

    stats_vec
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
