#![no_main]

use libfuzzer_sys::fuzz_target;

use btree_test_utils::{Operation, end_to_end_ops};

fuzz_target!(|batches: Vec<Vec<Operation>>| {
    end_to_end_ops(batches);
});
