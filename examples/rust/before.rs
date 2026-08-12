mod basic {
    pub fn checkout(total: u64) {
        validate(total);
        charge(total);
        receipt();
    }

    fn validate(_total: u64) {}

    fn charge(_total: u64) {}

    fn receipt() {}
}

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

fn run_dyn(storage: &dyn Store, order: Order) {
    validate(order);
    storage.save(order);
    finalize(order);
}

pub fn exercise(order: Order) {
    run(&Postgres, order);
    run(&S3, order);
    run_dyn(&Postgres, order);
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
