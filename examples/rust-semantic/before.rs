#[derive(Clone, Copy)]
pub struct Order;

trait Store {
    fn save(&self, order: Order);
}

struct Postgres;

impl Store for Postgres {
    fn save(&self, order: Order) {
        sql::insert(order);
    }
}

struct S3;

impl Store for S3 {
    fn save(&self, order: Order) {
        aws::sign(order);
    }
}

fn run<S: Store>(storage: &S, order: Order) {
    validate(order);
    storage.save(order);
    finalize(order);
}

pub fn exercise(order: Order) {
    run(&Postgres, order);
    run(&S3, order);
}

fn validate(_order: Order) {}
fn finalize(_order: Order) {}

mod sql {
    use super::Order;

    pub fn insert(_order: Order) {}
}

mod aws {
    use super::Order;

    pub fn sign(_order: Order) {}
}
