use core::cell::RefCell;

use arrayvec::ArrayVec;

use crate::hash::{PortableHash, PortableHasher};

use crate::errors::BTreeError;
use crate::node::{DEFAULT_MAX_CHILDREN, LeafNode, Node, NodeRef};
use crate::{
    db::DatabaseGet,
    node::{
        EMPTY_TREE_ROOT_HASH, InnerNodeSnapshot, InnerOuter, InnerOuterSnapshotOwned,
        InnerOuterSnapshotRef, NodeHash,
    },
    store::{Idx, Store},
};

// ---------------------------------------------------------------------------
// VerifiedSnapshot
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedSnapshot<K, V> {
    snapshot: Snapshot<K, V>,
    node_hashes: Box<[NodeHash]>,
    leaf_hashes: Box<[NodeHash]>,
}

impl<K: Clone + Ord + PortableHash, V: Clone + PortableHash> VerifiedSnapshot<K, V> {
    #[inline]
    pub fn empty() -> Self {
        Self {
            snapshot: Snapshot::empty(),
            node_hashes: Box::new([]),
            leaf_hashes: Box::new([]),
        }
    }

    #[inline]
    pub fn verify_snapshot(
        snapshot: Snapshot<K, V>,
        hasher: &mut impl PortableHasher<32>,
    ) -> Result<Self, &'static str> {
        snapshot.root_node_ref()?;

        let mut node_hashes = Vec::with_capacity(snapshot.branches.len());
        let mut leaf_hashes = Vec::with_capacity(snapshot.leaves.len());

        for leaf in snapshot.leaves.iter() {
            leaf.portable_hash(hasher);
            leaf_hashes.push(hasher.finalize_reset());
        }

        for node in snapshot.branches.iter() {
            let hash_of_child = |child: Idx| -> Result<&NodeHash, &'static str> {
                match snapshot.classify(child)? {
                    SnapshotRegion::Branch(i) => node_hashes
                        .get(i)
                        .ok_or("snapshot: child node index must be less than parent"),
                    SnapshotRegion::Leaf(i) => leaf_hashes
                        .get(i)
                        .ok_or("snapshot: child leaf does not exist"),
                    SnapshotRegion::Unvisited(i) => snapshot
                        .unvisited_nodes
                        .get(i)
                        .ok_or("snapshot: child unvisited node does not exist"),
                }
            };

            let child_hashes: ArrayVec<NodeHash, DEFAULT_MAX_CHILDREN> = node
                .children
                .iter()
                .map(|&c| hash_of_child(c).copied())
                .collect::<Result<_, _>>()?;

            node.portable_hash_iter(hasher, &child_hashes);
            node_hashes.push(hasher.finalize_reset());
        }

        Ok(VerifiedSnapshot {
            snapshot,
            node_hashes: node_hashes.into_boxed_slice(),
            leaf_hashes: leaf_hashes.into_boxed_slice(),
        })
    }

    #[inline]
    pub fn root_hash(&self) -> NodeHash {
        self.node_hashes
            .last()
            .copied()
            .or_else(|| self.leaf_hashes.first().copied())
            .or_else(|| self.snapshot.unvisited_nodes.first().copied())
            .unwrap_or(EMPTY_TREE_ROOT_HASH)
    }

    #[inline]
    pub(crate) fn root_node_ref(&self) -> Option<NodeRef> {
        self.snapshot
            .root_node_ref()
            .expect("ill-formed verified snapshot")
    }
}

impl<K: Clone + Ord + PortableHash, V: Clone + PortableHash> Store for VerifiedSnapshot<K, V> {
    type Key = K;
    type Value = V;

    #[inline]
    fn get_store_root_idx(&self) -> Option<Idx> {
        self.root_node_ref().map(|n| n.stored().unwrap())
    }

    #[inline]
    fn get_store_root_hash(&self) -> NodeHash {
        self.root_hash()
    }

    #[inline]
    fn calc_subtree_hash(
        &self,
        _: &mut impl PortableHasher<32>,
        node: Idx,
    ) -> Result<NodeHash, BTreeError> {
        match self.snapshot.classify(node).map_err(BTreeError::from)? {
            SnapshotRegion::Branch(i) => Ok(self.node_hashes[i]),
            SnapshotRegion::Leaf(i) => Ok(self.leaf_hashes[i]),
            SnapshotRegion::Unvisited(i) => Ok(self.snapshot.unvisited_nodes[i]),
        }
    }

    #[inline]
    fn get(&self, idx: Idx) -> Result<InnerOuterSnapshotRef<'_, K, V>, BTreeError> {
        match self.snapshot.classify(idx).map_err(BTreeError::from)? {
            SnapshotRegion::Branch(i) => {
                Ok(InnerOuterSnapshotRef::Inner(&self.snapshot.branches[i]))
            }
            SnapshotRegion::Leaf(i) => Ok(InnerOuterSnapshotRef::Outer(&self.snapshot.leaves[i])),
            SnapshotRegion::Unvisited(_) => Err("node is unvisited".into()),
        }
    }
}

// ---------------------------------------------------------------------------
// Snapshot
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Snapshot<K, V> {
    branches: Box<[InnerNodeSnapshot<K>]>,
    leaves: Box<[LeafNode<K, V>]>,
    unvisited_nodes: Box<[NodeHash]>,
}

impl<K, V> Default for Snapshot<K, V> {
    fn default() -> Self {
        Self::empty()
    }
}

enum SnapshotRegion {
    Branch(usize),
    Leaf(usize),
    Unvisited(usize),
}

impl<K, V> Snapshot<K, V> {
    #[inline]
    pub fn empty() -> Self {
        Self {
            branches: Box::new([]),
            leaves: Box::new([]),
            unvisited_nodes: Box::new([]),
        }
    }

    fn root_node_ref(&self) -> Result<Option<NodeRef>, &'static str> {
        match (
            self.branches.as_ref(),
            self.leaves.as_ref(),
            self.unvisited_nodes.as_ref(),
        ) {
            ([], [], []) => Ok(None),
            ([.., _], _, _) => Ok(Some(NodeRef::Stored(self.branches.len() as Idx - 1))),
            ([], [_], []) | ([], [], [_]) => Ok(Some(NodeRef::Stored(0))),
            _ => Err("ill-formed snapshot"),
        }
    }

    fn classify(&self, idx: Idx) -> Result<SnapshotRegion, &'static str> {
        let i = idx as usize;
        let leaf_offset = self.branches.len();
        let unvisited_offset = leaf_offset + self.leaves.len();
        if i < leaf_offset {
            Ok(SnapshotRegion::Branch(i))
        } else if i - leaf_offset < self.leaves.len() {
            Ok(SnapshotRegion::Leaf(i - leaf_offset))
        } else if i - unvisited_offset < self.unvisited_nodes.len() {
            Ok(SnapshotRegion::Unvisited(i - unvisited_offset))
        } else {
            Err("node does not exist")
        }
    }
}

// ---------------------------------------------------------------------------
// AppendOnlyVec — enforces push-only access at the type level
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct AppendOnlyVec<T>(Vec<T>);

impl<T> AppendOnlyVec<T> {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn push(&mut self, val: T) {
        self.0.push(val);
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn get(&self, idx: usize) -> Option<&T> {
        self.0.get(idx)
    }

    fn first(&self) -> Option<&T> {
        self.0.first()
    }

    fn as_slice(&self) -> &[T] {
        &self.0
    }
}

impl<T> core::ops::Index<usize> for AppendOnlyVec<T> {
    type Output = T;
    fn index(&self, idx: usize) -> &T {
        &self.0[idx]
    }
}

impl<T> core::ops::IndexMut<usize> for AppendOnlyVec<T> {
    fn index_mut(&mut self, idx: usize) -> &mut T {
        &mut self.0[idx]
    }
}

// ---------------------------------------------------------------------------
// SnapshotBuilder  (Vec replaces imbl::Vector, direct ownership replaces Arc)
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct SnapshotBuilder<K: Ord + Clone + PortableHash, V: Clone + PortableHash, Db> {
    pub db: Db,
    inner: RefCell<SnapshotBuilderInner<K, V>>,
}

#[derive(Clone)]
struct SnapshotBuilderInner<K, V> {
    nodes: AppendOnlyVec<(NodeHash, Option<InnerOuterSnapshotOwned<K, V>>)>,
}

impl<K: Ord + Clone + PortableHash, V: Clone + PortableHash, Db> SnapshotBuilder<K, V, Db> {
    #[inline]
    pub fn new(root: NodeHash, db: Db) -> Self {
        let mut nodes = AppendOnlyVec::new();
        if root != EMPTY_TREE_ROOT_HASH {
            nodes.push((root, None));
        }
        Self {
            db,
            inner: RefCell::new(SnapshotBuilderInner { nodes }),
        }
    }

    pub fn root_hash(&self) -> NodeHash {
        self.inner
            .borrow()
            .nodes
            .first()
            .map(|(h, _)| *h)
            .unwrap_or(EMPTY_TREE_ROOT_HASH)
    }

    pub fn build_initial_snapshot(&self) -> Snapshot<K, V> {
        let inner = self.inner.borrow();
        if inner.nodes.is_empty() {
            return Snapshot::empty();
        }

        let mut state = SnapshotBuilderFold::new(inner.nodes.as_slice());
        let root_idx = state.fold(0);

        debug_assert!(state.branches.is_empty() || root_idx == state.branches.len() as Idx - 1);
        state.build()
    }
}

impl<K: Ord + Clone + PortableHash, V: Clone + PortableHash, Db: DatabaseGet<K, V>> Store
    for SnapshotBuilder<K, V, Db>
{
    type Key = K;
    type Value = V;

    #[inline]
    fn get_store_root_idx(&self) -> Option<Idx> {
        if self.inner.borrow().nodes.is_empty() {
            None
        } else {
            Some(0)
        }
    }

    #[inline]
    fn get_store_root_hash(&self) -> NodeHash {
        self.root_hash()
    }

    fn calc_subtree_hash(
        &self,
        _hasher: &mut impl PortableHasher<32>,
        hash_idx: Idx,
    ) -> Result<NodeHash, BTreeError> {
        let inner = self.inner.borrow();
        let (h, _) = inner
            .nodes
            .get(hash_idx as usize)
            .ok_or("Hash Index out of bounds")?;
        Ok(*h)
    }

    fn get(&self, hash_idx: Idx) -> Result<InnerOuterSnapshotRef<'_, K, V>, BTreeError> {
        let mut inner = self.inner.borrow_mut();
        let idx = hash_idx as usize;
        let (hash, opt) = inner
            .nodes
            .get(idx)
            .ok_or("Index out of bounds")
            .map(|(h, o)| (*h, o.is_none()))?;

        if opt {
            let newly_read = self.db.get(&hash).map_err(|e| e.to_string())?;
            match newly_read {
                InnerOuter::Inner(node) => {
                    let children = node
                        .children
                        .iter()
                        .map(|child_hash| {
                            let child_idx = inner.nodes.len() as Idx;
                            inner.nodes.push((*child_hash, None));
                            child_idx
                        })
                        .collect();

                    inner.nodes[idx].1 = Some(InnerOuterSnapshotOwned::Inner(Node {
                        keys: node.keys,
                        children,
                    }));
                }
                InnerOuter::Outer(leaf) => {
                    inner.nodes[idx].1 = Some(InnerOuterSnapshotOwned::Outer(leaf.clone()));
                }
            }
        }

        let node_or_leaf = inner.nodes[idx].1.as_ref().unwrap();

        // Safety: AppendOnlyVec guarantees elements are never removed or relocated
        // (only push is exposed). The SnapshotBuilder outlives the returned reference.
        unsafe {
            match node_or_leaf {
                InnerOuter::Inner(node) => Ok(InnerOuterSnapshotRef::Inner(&*(node as *const _))),
                InnerOuter::Outer(leaf) => Ok(InnerOuterSnapshotRef::Outer(&*(leaf as *const _))),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SnapshotBuilderFold
// ---------------------------------------------------------------------------

struct SnapshotBuilderFold<'a, K, V> {
    nodes: &'a [(NodeHash, Option<InnerOuterSnapshotOwned<K, V>>)],
    branch_count: u32,
    leaf_count: u32,
    branches: Vec<Node<K, Idx>>,
    leaves: Vec<LeafNode<K, V>>,
    unvisited_nodes: Vec<NodeHash>,
}

impl<'a, K: Clone, V: Clone> SnapshotBuilderFold<'a, K, V> {
    fn new(nodes: &'a [(NodeHash, Option<InnerOuterSnapshotOwned<K, V>>)]) -> Self {
        let mut branch_count = 0u32;
        let mut leaf_count = 0u32;
        let mut unvisited_count = 0u32;
        for (_, opt) in nodes.iter() {
            match opt {
                Some(InnerOuter::Inner(_)) => branch_count += 1,
                Some(InnerOuter::Outer(_)) => leaf_count += 1,
                None => unvisited_count += 1,
            }
        }
        SnapshotBuilderFold {
            nodes,
            branch_count,
            leaf_count,
            branches: Vec::with_capacity(branch_count as usize),
            leaves: Vec::with_capacity(leaf_count as usize),
            unvisited_nodes: Vec::with_capacity(unvisited_count as usize),
        }
    }

    fn fold(&mut self, node_idx: Idx) -> Idx {
        let entry = &self.nodes[node_idx as usize];
        match &entry.1 {
            Some(InnerOuter::Inner(branch)) => {
                let keys = branch.keys.clone();
                let children = branch
                    .children
                    .iter()
                    .map(|&child_idx| self.fold(child_idx))
                    .collect();
                let idx = self.branches.len() as Idx;
                self.branches.push(Node { keys, children });
                idx
            }
            Some(InnerOuter::Outer(leaf)) => {
                let idx = self.leaves.len() as Idx;
                self.leaves.push(leaf.clone());
                self.branch_count + idx
            }
            None => {
                let idx = self.unvisited_nodes.len() as Idx;
                self.unvisited_nodes.push(entry.0);
                self.branch_count + self.leaf_count + idx
            }
        }
    }

    fn build(self) -> Snapshot<K, V> {
        Snapshot {
            branches: self.branches.into_boxed_slice(),
            leaves: self.leaves.into_boxed_slice(),
            unvisited_nodes: self.unvisited_nodes.into_boxed_slice(),
        }
    }
}
