pub fn run(order: u64) {
    let persist = |value| {
        write(value);
    };
    persist(order);
}

fn write(_value: u64) {}
