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
