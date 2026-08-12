mod basic {
    pub fn checkout(total: u64) {
        prepare(total);
        charge(total);
    }

    fn prepare(total: u64) {
        validate(total);
        reserve();
    }

    fn validate(_total: u64) {}

    fn reserve() {}

    fn charge(_total: u64) {}
}

#[derive(Clone, Copy)]
pub struct Order;

trait Store {
    fn save(&self, order: Order);
}

struct Postgres;

impl Store for Postgres {
    fn save(&self, order: Order) {
        sql::begin();
        sql::insert(order);
        sql::commit();
    }
}

struct S3;

impl Store for S3 {
    fn save(&self, order: Order) {
        aws::sign(order);
        aws::put_object(order);
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
    run_dyn(&S3, order);
}

fn validate(_order: Order) {}
fn finalize(_order: Order) {}

mod sql {
    use super::Order;

    pub fn begin() {}
    pub fn insert(_order: Order) {}
    pub fn commit() {}
}

mod aws {
    use super::Order;

    pub fn sign(_order: Order) {}
    pub fn put_object(_order: Order) {}
}
