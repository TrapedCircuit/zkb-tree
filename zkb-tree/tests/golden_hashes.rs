use sha2::Sha256;
use zkb_tree::{DigestHasher, NodeHash, Transaction, db::MemoryDb};

fn compute_root(ops: &[(bool, u32, u32)]) -> NodeHash {
    let mut txn =
        Transaction::new_snapshot_builder_txn(Default::default(), MemoryDb::<u32, u32>::default());
    let hasher = &mut DigestHasher::<Sha256>::default();
    for &(is_insert, k, v) in ops {
        if is_insert {
            txn.insert(k, v).unwrap();
        } else {
            txn.remove(&k).unwrap();
        }
    }
    txn.calc_root_hash(hasher).unwrap()
}

/// Golden values captured after Phase 3 (hash with length prefix).
#[test]
fn golden_hash_three_inserts() {
    let root = compute_root(&[(true, 0, 0), (true, 1, 1), (true, 2, 2)]);
    let expected: NodeHash = [
        245, 28, 191, 119, 219, 38, 119, 154, 224, 57, 204, 165, 79, 61, 99, 41, 170, 8, 72, 57,
        53, 86, 18, 39, 247, 76, 216, 15, 23, 171, 122, 168,
    ];
    assert_eq!(root, expected);
}

#[test]
fn golden_hash_insert_then_delete() {
    let root = compute_root(&[(true, 0, 0), (true, 1, 1), (true, 2, 2), (false, 1, 0)]);
    let expected: NodeHash = [
        135, 133, 100, 216, 27, 103, 11, 155, 59, 96, 28, 229, 163, 74, 57, 101, 204, 42, 134, 182,
        218, 235, 113, 146, 24, 124, 193, 95, 45, 128, 25, 2,
    ];
    assert_eq!(root, expected);
}

#[test]
fn golden_hash_twenty_five_inserts() {
    let ops: Vec<(bool, u32, u32)> = (0..25u32).map(|k| (true, k, k * 10)).collect();
    let root = compute_root(&ops);
    let expected: NodeHash = [
        14, 101, 143, 98, 119, 179, 222, 41, 130, 59, 36, 230, 187, 100, 155, 77, 145, 135, 161,
        45, 184, 99, 20, 77, 203, 110, 28, 139, 173, 5, 221, 186,
    ];
    assert_eq!(root, expected);
}
