pub fn checkout(total: u64) {
    validate(total);
    charge(total);
    receipt();
}

fn validate(_total: u64) {}

fn charge(_total: u64) {}

fn receipt() {}
