use std::rc::Rc;

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use sha2::Sha256;
use zkb_tree::{
    DigestHasher, NodeHash, Transaction, VerifiedSnapshot, db::MemoryDb, snapshot::Snapshot,
};

fn build_tree(size: u32) -> (NodeHash, Rc<MemoryDb<u32, u32>>) {
    let db = Rc::new(MemoryDb::<u32, u32>::default());
    let mut txn = Transaction::new_snapshot_builder_txn(Default::default(), db.clone());
    for k in 0..size {
        txn.insert(k, k).unwrap();
    }
    let root = txn.commit(&mut DigestHasher::<Sha256>::default()).unwrap();
    (root, db)
}

fn build_tree_and_snapshot(
    size: u32,
    touch_count: u32,
) -> (NodeHash, Snapshot<u32, u32>, NodeHash) {
    let (old_root, db) = build_tree(size);
    let mut txn = Transaction::new_snapshot_builder_txn(old_root, db);
    for k in 0..touch_count {
        txn.insert(k, k + size).unwrap();
    }
    let new_root = txn.commit(&mut DigestHasher::<Sha256>::default()).unwrap();
    let snapshot = txn.build_initial_snapshot();
    (old_root, snapshot, new_root)
}

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    for size in [1_000u32, 10_000, 100_000] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter(|| {
                let mut txn = Transaction::new_snapshot_builder_txn(
                    Default::default(),
                    MemoryDb::<u32, u32>::default(),
                );
                for k in 0..size {
                    txn.insert(black_box(k), black_box(k)).unwrap();
                }
            });
        });
    }
    group.finish();
}

fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("get");
    for size in [1_000u32, 10_000, 100_000] {
        let (root, db) = build_tree(size);
        let txn = Transaction::new_snapshot_builder_txn(root, db);
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter(|| {
                for k in 0..size {
                    black_box(txn.get(black_box(&k)).unwrap());
                }
            });
        });
    }
    group.finish();
}

fn bench_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("remove");
    for size in [1_000u32, 10_000] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let (root, db) = build_tree(size);
                    Transaction::new_snapshot_builder_txn(root, db)
                },
                |mut txn| {
                    for k in 0..size / 2 {
                        txn.remove(black_box(&k)).unwrap();
                    }
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

fn bench_range(c: &mut Criterion) {
    let mut group = c.benchmark_group("range");
    for size in [1_000u32, 10_000, 100_000] {
        let (root, db) = build_tree(size);
        let txn = Transaction::new_snapshot_builder_txn(root, db);
        let range_size = size / 10;
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, _| {
            b.iter(|| {
                let count = txn.range(black_box(0u32)..black_box(range_size)).count();
                black_box(count);
            });
        });
    }
    group.finish();
}

fn bench_commit(c: &mut Criterion) {
    let mut group = c.benchmark_group("commit");
    for size in [1_000u32, 10_000, 100_000] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let mut txn = Transaction::new_snapshot_builder_txn(
                        Default::default(),
                        MemoryDb::<u32, u32>::default(),
                    );
                    for k in 0..size {
                        txn.insert(k, k).unwrap();
                    }
                    txn
                },
                |txn| {
                    black_box(txn.commit(&mut DigestHasher::<Sha256>::default()).unwrap());
                },
                criterion::BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

fn bench_verify_snapshot(c: &mut Criterion) {
    let mut group = c.benchmark_group("verify_snapshot");
    for size in [1_000u32, 10_000, 100_000] {
        let touch_count = size / 10;
        let (_old_root, snapshot, _new_root) = build_tree_and_snapshot(size, touch_count);
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, _| {
            b.iter_batched(
                || snapshot.clone(),
                |snap| {
                    black_box(
                        VerifiedSnapshot::verify_snapshot(
                            black_box(snap),
                            &mut DigestHasher::<Sha256>::default(),
                        )
                        .unwrap(),
                    );
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

fn bench_end_to_end(c: &mut Criterion) {
    let mut group = c.benchmark_group("end_to_end");
    for size in [1_000u32, 10_000] {
        let touch_count = size / 10;
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter(|| {
                let db = Rc::new(MemoryDb::<u32, u32>::default());
                let mut txn = Transaction::new_snapshot_builder_txn(Default::default(), db.clone());
                for k in 0..size {
                    txn.insert(k, k).unwrap();
                }
                let old_root = txn.commit(&mut DigestHasher::<Sha256>::default()).unwrap();
                let mut txn = Transaction::new_snapshot_builder_txn(old_root, db);
                for k in 0..touch_count {
                    txn.insert(k, k + size).unwrap();
                }
                let new_root = txn.commit(&mut DigestHasher::<Sha256>::default()).unwrap();
                let snapshot = txn.build_initial_snapshot();

                let verified = VerifiedSnapshot::verify_snapshot(
                    snapshot,
                    &mut DigestHasher::<Sha256>::default(),
                )
                .unwrap();
                assert_eq!(old_root, verified.root_hash());

                let mut replay_txn = Transaction::from_verified_snapshot_ref(&verified);
                for k in 0..touch_count {
                    replay_txn.insert(k, k + size).unwrap();
                }
                let replay_root = replay_txn
                    .calc_root_hash(&mut DigestHasher::<Sha256>::default())
                    .unwrap();
                assert_eq!(new_root, replay_root);
            });
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_insert,
    bench_get,
    bench_remove,
    bench_range,
    bench_commit,
    bench_verify_snapshot,
    bench_end_to_end,
);
criterion_main!(benches);
