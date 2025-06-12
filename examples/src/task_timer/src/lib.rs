//! An example showcasing how to use a MinHeap for scheduled tasks.
use ic_cdk_macros::{post_upgrade, update};
use ic_stable_structures::memory_manager::{MemoryId, MemoryManager, VirtualMemory};
use ic_stable_structures::{DefaultMemoryImpl, StableMinHeap};
use std::cell::RefCell;

type Memory = VirtualMemory<DefaultMemoryImpl>;

thread_local! {
    static MEMORY_MANAGER: RefCell<MemoryManager<DefaultMemoryImpl>> =
        RefCell::new(MemoryManager::init(DefaultMemoryImpl::default()));

    static TASKS: RefCell<StableMinHeap<u64, Memory>> =
        MEMORY_MANAGER.with(|mm|
            RefCell::new(
                StableMinHeap::init(mm.borrow().get(MemoryId::new(1)))
                .expect("failed to initialize the tasks"))
        );
}

#[post_upgrade]
fn post_upgrade() {
    reschedule();
}

#[update]
fn schedule_task(after_sec: u64) {
    let task_time = ic_cdk::api::time() + after_sec * 1_000_000_000;
    TASKS.with(|t| {
        t.borrow_mut()
            .push(&task_time)
            .expect("failed to schedule a task")
    });
    reschedule();
}

#[export_name = "canister_global_timer"]
fn timer() {
    let now = ic_cdk::api::time();
    while let Some(task_time) = TASKS.with(|t| t.borrow().peek()) {
        if task_time > now {
            reschedule();
            return;
        }
        let _ = TASKS.with(|t| t.borrow_mut().pop());

        execute_task(task_time, now);
        reschedule();
    }
}

fn execute_task(scheduled_at: u64, now: u64) {
    ic_cdk::println!("executing task scheculed at {scheduled_at}, current time is {now}");
}

fn reschedule() {
    if let Some(task_time) = TASKS.with(|t| t.borrow().peek()) {
        unsafe {
            ic0::global_timer_set(task_time as u64);
        }
    }
}
