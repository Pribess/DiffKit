use crate::storage::{Postgres, Store};

#[derive(Clone, Copy)]
pub struct Order;

pub fn entry(order: Order) {
    run(&Postgres, order);
}

fn run<S: Store>(storage: &S, order: Order) {
    storage.save(order);
}

pub fn detached<S: Store>(storage: &S, order: Order) {
    storage.save(order);
}
