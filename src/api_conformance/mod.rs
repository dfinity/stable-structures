use std::cell::RefCell;
use std::rc::Rc;

#[cfg(test)]
mod btreemap;

#[cfg(test)]
mod btreeset;

#[cfg(test)]
mod min_heap;

#[cfg(test)]
mod vec;

#[cfg(test)]
pub(crate) fn make_memory() -> Rc<RefCell<std::vec::Vec<u8>>> {
    Rc::new(RefCell::new(std::vec::Vec::new()))
}
