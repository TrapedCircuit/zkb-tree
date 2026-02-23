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
pub struct VerifiedSnapshot<S: Store> {
    snapshot: S,
    node_hashes: Box<[NodeHash]>,
    leaf_hashes: Box<[NodeHash]>,
}

impl<S: Store + Default> Default for VerifiedSnapshot<S> {
    #[inline]
    fn default() -> Self {
        Self {
            snapshot: S::default(),
            node_hashes: Box::new([]),
            leaf_hashes: Box::new([]),
        }
    }
}

impl<S: Store + AsRef<Snapshot<S::Key, S::Value>>> VerifiedSnapshot<S> {
    #[inline]
    pub fn empty() -> Self
    where
        S: Default,
    {
        Self::default()
    }

    #[inline]
    pub fn verify_snapshot(
        snapshot: S,
        hasher: &mut impl PortableHasher<32>,
    ) -> Result<Self, &'static str> {
        let snap = snapshot.as_ref();
        snap.root_node_ref()?;

        let mut node_hashes = Vec::with_capacity(snap.branches.len());
        let mut leaf_hashes = Vec::with_capacity(snap.leaves.len());

        for leaf in snap.leaves.iter() {
            leaf.portable_hash(hasher);
            leaf_hashes.push(hasher.finalize_reset());
        }

        let leaf_offset = snap.branches.len();
        let unvisited_offset = leaf_offset + snap.leaves.len();

        for node in snap.branches.iter() {
            let hash_of_child = |child: usize| -> Result<&NodeHash, &'static str> {
                if child < leaf_offset {
                    node_hashes
                        .get(child)
                        .ok_or("snapshot: child node index must be less than parent")
                } else if child < unvisited_offset {
                    leaf_hashes
                        .get(child - leaf_offset)
                        .ok_or("snapshot: child leaf does not exist")
                } else {
                    snap.unvisited_nodes
                        .get(child - unvisited_offset)
                        .ok_or("snapshot: child unvisited node does not exist")
                }
            };

            let child_hashes: ArrayVec<NodeHash, DEFAULT_MAX_CHILDREN> = node
                .children
                .iter()
                .map(|&c| hash_of_child(c as usize).copied())
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
            .or_else(|| self.snapshot.as_ref().unvisited_nodes.first().copied())
            .unwrap_or(EMPTY_TREE_ROOT_HASH)
    }

    #[inline]
    pub(crate) fn root_node_ref(&self) -> Option<NodeRef> {
        self.snapshot
            .as_ref()
            .root_node_ref()
            .expect("ill-formed verified snapshot")
    }
}

impl<S: Store + AsRef<Snapshot<S::Key, S::Value>>> Store for VerifiedSnapshot<S> {
    type Key = S::Key;
    type Value = S::Value;

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
        let snap = self.snapshot.as_ref();
        let idx = node as usize;
        let leaf_offset = snap.branches.len();
        let unvisited_offset = leaf_offset + snap.leaves.len();

        if let Some(h) = self.node_hashes.get(idx) {
            Ok(*h)
        } else if let Some(h) = self.leaf_hashes.get(idx - leaf_offset) {
            Ok(*h)
        } else if let Some(h) = snap.unvisited_nodes.get(idx - unvisited_offset) {
            Ok(*h)
        } else {
            Err("node does not exist".into())
        }
    }

    #[inline]
    fn get(
        &self,
        idx: Idx,
    ) -> Result<InnerOuterSnapshotRef<'_, Self::Key, Self::Value>, BTreeError> {
        let snap = self.snapshot.as_ref();
        let i = idx as usize;
        let leaf_offset = snap.branches.len();
        let unvisited_offset = leaf_offset + snap.leaves.len();

        if let Some(n) = snap.branches.get(i) {
            Ok(InnerOuterSnapshotRef::Inner(n))
        } else if let Some(l) = snap.leaves.get(i - leaf_offset) {
            Ok(InnerOuterSnapshotRef::Outer(l))
        } else if snap.unvisited_nodes.get(i - unvisited_offset).is_some() {
            Err("node is unvisited".into())
        } else {
            Err("node does not exist".into())
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
}

impl<K, V> AsRef<Snapshot<K, V>> for Snapshot<K, V> {
    fn as_ref(&self) -> &Snapshot<K, V> {
        self
    }
}

impl<K: Clone + Ord + PortableHash, V: Clone + PortableHash> Store for Snapshot<K, V> {
    type Key = K;
    type Value = V;

    fn get_store_root_idx(&self) -> Option<Idx> {
        unimplemented!("Use VerifiedSnapshot to get the root index of a snapshot")
    }

    fn get_store_root_hash(&self) -> NodeHash {
        unimplemented!("Use VerifiedSnapshot to get the root hash of a snapshot")
    }

    fn calc_subtree_hash(
        &self,
        _hasher: &mut impl PortableHasher<32>,
        _hash_idx: Idx,
    ) -> Result<NodeHash, BTreeError> {
        unimplemented!("Use VerifiedSnapshot to calculate the hash of a snapshot")
    }

    fn get(
        &self,
        hash_idx: Idx,
    ) -> Result<InnerOuterSnapshotRef<'_, Self::Key, Self::Value>, BTreeError> {
        let idx = hash_idx as usize;
        if let Some(n) = self.branches.get(idx) {
            Ok(InnerOuterSnapshotRef::Inner(n))
        } else if let Some(l) = self.leaves.get(idx - self.branches.len()) {
            Ok(InnerOuterSnapshotRef::Outer(l))
        } else {
            Err("node does not exist".into())
        }
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
    nodes: Vec<(NodeHash, Option<InnerOuterSnapshotOwned<K, V>>)>,
}

impl<K: Ord + Clone + PortableHash, V: Clone + PortableHash, Db> SnapshotBuilder<K, V, Db> {
    #[inline]
    pub fn new(root: NodeHash, db: Db) -> Self {
        if root == EMPTY_TREE_ROOT_HASH {
            Self {
                db,
                inner: RefCell::new(SnapshotBuilderInner { nodes: Vec::new() }),
            }
        } else {
            Self {
                db,
                inner: RefCell::new(SnapshotBuilderInner {
                    nodes: vec![(root, None)],
                }),
            }
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

        let mut state = SnapshotBuilderFold::new(&inner.nodes);
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

        // Safety: The SnapshotBuilder's inner Vec only grows (push, never remove/reorder).
        // The SnapshotBuilder outlives the returned reference. So the pointer remains valid.
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
