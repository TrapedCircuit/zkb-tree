# AGENTS.md — Coding Guidelines for zkvm-merkle-trees

## Project Overview

A Merkle B+Tree for zkVM state verification. The prover builds minimal snapshots of tree operations; the verifier replays them inside a zkVM to confirm Merkle roots.

## Architecture

- **`zkb-tree`** — the main crate
  - `node.rs` — `Node<K, NR, MAX>`, `NodeRef` (Copy, index-based), `NodeArena` (slab-based), merge/balance logic
  - `transaction.rs` — `Transaction<S: Store>` with insert/remove/get/range/iter, hash computation, commit
  - `snapshot.rs` — `Snapshot`, `VerifiedSnapshot`, `SnapshotBuilder` (lazy-loading from DB via `RefCell`)
  - `store.rs` — `Store` trait (abstract read access to snapshots)
  - `db.rs` — `DatabaseGet`/`DatabaseSet` traits, `MemoryDb` implementation
  - `hash.rs` — `PortableHash`, `PortableHasher`, `DigestHasher` (platform-independent hashing)
  - `errors.rs` — `BTreeError`
- **`btree-test-utils`** — shared test utilities (`Operation` enum, `end_to_end_ops`)
- **`fuzz/`** — libFuzzer target (`btree_ops`)
- **`fuzz-afl/`** — AFL target (`btree_ops_afl`), excluded from workspace

## Key Design Decisions

### Slab-based arena allocation
All tree nodes live in `NodeArena<K, V>` which wraps two `slab::Slab` instances (one for inner nodes, one for leaves). `NodeRef` is a lightweight `Copy` enum holding a `u32` index. No `Arc`, no per-node heap allocation. The arena is owned by `Transaction` and dropped when the transaction ends.

### Hash includes length prefix
`portable_hash` and `portable_hash_iter` emit `keys.len()` and `children.len()` as u32 before the actual data. This prevents ambiguous hash collisions between nodes of different sizes.

### Configurable node capacity
`Node<K, NR, const MAX: usize = DEFAULT_MAX_CHILDREN>` allows customizing the B+Tree order via the const generic. `DEFAULT_MAX_CHILDREN = 20` (order 10). The `min_children()`, `min_keys()` etc. derive from `MAX`.

### SnapshotBuilder unsafe
`SnapshotBuilder::get()` uses `unsafe` to extend the lifetime of references obtained through `RefCell::borrow_mut()`. This is sound because the inner `Vec` only grows (push, never remove/reorder) and the `SnapshotBuilder` outlives all returned references.

## Coding Conventions

- **No `Arc` in tree nodes** — use `NodeArena` indices instead
- **Sequential borrows for multi-node mutation** — drain one node's data into a temporary `Vec`, then extend the other. Never hold two `&mut` into the same `Slab` simultaneously.
- **`#[cfg(debug_assertions)]`** for invariant checks — `assert_inner_invariants()`, `assert_leaf_invariants()` are called in debug builds only
- **`#[inline]` / `#[inline(always)]`** on hot-path accessors (arena indexing, hash functions)
- **Prefer `ArrayVec`** over `Vec` for node storage (stack-allocated, fixed capacity)

## Testing

Run all tests:
```bash
cargo test
```

Run benchmarks:
```bash
cargo bench --bench btree_bench
```

Run fuzz (60 seconds):
```bash
./scripts/fuzz.sh
```

### Test layers
1. Unit tests in `node.rs` (arena allocation, hash consistency)
2. Unit tests in `transaction.rs` (hardcoded insert/remove/range scenarios against `BTreeMap`)
3. Property tests via proptest (random operations, 1-10K ops per run)
4. Golden hash regression tests (`tests/golden_hashes.rs`)
5. Snapshot round-trip tests (`tests/snapshot_tests.rs`)
6. Multi-batch end-to-end via `btree-test-utils` (`tests/multi_batch_proptest.rs`)
7. Fuzz testing via libFuzzer and AFL

### After making changes
- Run `cargo test` — all 31 tests must pass
- Run `cargo clippy` — no warnings
- If node hashing logic changed, update golden hashes in `tests/golden_hashes.rs`
- If public API changed, check `btree-test-utils` and fuzz targets compile

## Module Dependency Graph

```
lib.rs
 ├── hash.rs          (no internal deps)
 ├── errors.rs        (no internal deps)
 ├── store.rs         (depends on: hash, errors, node)
 ├── db.rs            (depends on: node)
 ├── node.rs          (depends on: hash, store, errors)
 ├── snapshot.rs      (depends on: hash, errors, node, db, store)
 └── transaction.rs   (depends on: hash, errors, node, db, store, snapshot)
```

## Common Tasks

### Adding a new B+Tree operation
1. Add method to `Transaction<S: Store>` in `transaction.rs`
2. Add variant to `Operation` in `btree-test-utils/src/lib.rs`
3. Add handling in `run_against_snapshot_builder` and `merkle_btree_op`
4. Add to proptest strategy
5. Run `cargo test` and `./scripts/fuzz.sh btree 30`

### Changing the hash scheme
1. Update `portable_hash` and `portable_hash_iter` in `node.rs`
2. Regenerate golden hashes: run tests, copy new values from failure output
3. All stored snapshots become invalid — this is a breaking change

### Changing BTREE_ORDER
1. Modify `BTREE_ORDER` and `DEFAULT_MAX_CHILDREN` in `node.rs`
2. All stored data becomes incompatible (different tree shape = different hashes)
3. Alternatively, use `Node<K, NR, 30>` for a custom capacity without changing the default
