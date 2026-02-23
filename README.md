# zkb-tree

A Merkle B+Tree implementation optimized for zero-knowledge virtual machines (zkVMs).

## Overview

`zkb-tree` provides a verifiable ordered key-value store built on a B+Tree (order 10, configurable). It is designed for the prover/verifier pattern common in zkVM applications: the prover builds a minimal snapshot of the tree, and the verifier replays operations against that snapshot to confirm the new Merkle root.

Key properties:

- **Ordered keys** with `get`, `insert`, `remove`, `range`, `iter`, `first_key_value`, `last_key_value`
- **Minimal snapshots** — only nodes touched by a transaction are included
- **Portable hashing** — deterministic across platforms via `PortableHash` traits
- **Slab-based arena allocation** — nodes are indexed by lightweight `u32` handles (no `Arc`, no per-node heap allocation)
- **Configurable node capacity** — `Node<K, NR, const MAX>` defaults to 20 children (order 10)

## Architecture

```
┌─────────────────────────────────────────────────┐
│  Transaction<S: Store>                          │
│  ┌───────────┐  ┌──────────────────────────┐    │
│  │ data_store│  │ NodeArena (Slab-based)    │    │
│  │ (Snapshot │  │  inner_nodes: Slab<Node>  │    │
│  │  Builder) │  │  leaf_nodes:  Slab<Node>  │    │
│  └───────────┘  └──────────────────────────┘    │
│  current_root: Option<NodeRef>                  │
│    NodeRef::Inner(u32) | Leaf(u32) | Stored(Idx)│
└─────────────────────────────────────────────────┘
```

**Prover side** (server):
```rust
let db = MemoryDb::default();
let mut txn = Transaction::new_snapshot_builder_txn(old_root, db);
txn.insert(key, value)?;
let new_root = txn.commit(&mut hasher)?;
let snapshot = txn.build_initial_snapshot();
// send (snapshot, new_root) to verifier
```

**Verifier side** (zkVM):
```rust
let verified = VerifiedSnapshot::verify_snapshot(&snapshot, &mut hasher)?;
assert_eq!(verified.root_hash(), expected_old_root);
let mut txn = Transaction::from_verified_snapshot_ref(&verified);
txn.insert(key, value)?;
let computed_root = txn.calc_root_hash(&mut hasher)?;
assert_eq!(computed_root, expected_new_root);
```

## Workspace Structure

```
zkvm-merkle-trees/
├── zkb-tree/                   # Main library crate
│   ├── src/
│   │   ├── node.rs             # Node, NodeRef, NodeArena, merge/balance
│   │   ├── transaction.rs      # Transaction (insert/remove/get/range/iter)
│   │   ├── snapshot.rs         # Snapshot, VerifiedSnapshot, SnapshotBuilder
│   │   ├── store.rs            # Store trait
│   │   ├── db.rs               # DatabaseGet/Set traits, MemoryDb
│   │   ├── hash.rs             # PortableHash, DigestHasher
│   │   ├── errors.rs           # BTreeError
│   │   └── lib.rs              # Public API re-exports
│   ├── benches/
│   │   └── btree_bench.rs      # Criterion benchmarks
│   ├── tests/
│   │   ├── golden_hashes.rs    # Merkle root regression tests
│   │   ├── snapshot_tests.rs   # Snapshot round-trip tests
│   │   └── multi_batch_proptest.rs  # Multi-batch property tests
│   └── btree-test-utils/       # Shared test utilities (Operation, end_to_end_ops)
├── fuzz/                       # libFuzzer targets (cargo-fuzz)
├── fuzz-afl/                   # AFL fuzzer targets
├── scripts/
│   └── fuzz.sh                 # Fuzz testing script
└── .github/workflows/rust.yml  # CI (build, test, fuzz)
```

## Building

```bash
# Build
cargo build

# Build without std (no_std)
cargo build --no-default-features

# Run tests
cargo test

# Run benchmarks
cargo bench --bench btree_bench

# Run fuzz tests (30 seconds)
./scripts/fuzz.sh btree 30
```

## Benchmarks

Measured on Apple Silicon (M-series), release profile:

| Operation | 1K keys | 10K keys | 100K keys |
|-----------|---------|----------|-----------|
| insert | 25 us | 371 us | 4.9 ms |
| get | 30 us | 440 us | 5.9 ms |
| remove | 34 us | 427 us | - |
| range (10%) | 348 ns | 3.0 us | 29 us |
| commit | 50 us | 563 us | 6.8 ms |
| verify_snapshot | 4.8 us | 40 us | 389 us |

## Testing

The crate has multiple layers of testing:

- **Unit tests** — hardcoded scenarios in `transaction.rs` and arena invariant tests in `node.rs`
- **Property tests** — proptest with random operations, verified against `std::BTreeMap`
- **Golden hash tests** — Merkle root determinism regression guard
- **Snapshot round-trip tests** — build snapshot, verify, replay, confirm root matches
- **Multi-batch integration tests** — multi-batch prover/verifier end-to-end via `btree-test-utils`
- **Fuzz testing** — libFuzzer (`cargo fuzz`) and AFL, with accumulated corpus

## Features

- `std` (default) — standard library support
- `serde` — serialization for `Node`, `Snapshot`, `InnerOuter` via serde
# zkb-tree
# zkb-tree
