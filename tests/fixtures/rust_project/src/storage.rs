use crate::service::Order;

pub trait Store {
    fn save(&self, order: Order);
}

pub struct Postgres;

impl Store for Postgres {
    fn save(&self, order: Order) {
        write(order);
    }
}

fn write(_order: Order) {}
