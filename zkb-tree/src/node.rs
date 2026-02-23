use alloc::vec::Vec;

use arrayvec::ArrayVec;
use slab::Slab;

use crate::hash::{PortableHash, PortableUpdate};
use crate::store::Idx;

pub const BTREE_ORDER: usize = 10;
pub const DEFAULT_MAX_CHILDREN: usize = BTREE_ORDER * 2;
pub const EMPTY_TREE_ROOT_HASH: [u8; 32] = [0; 32];

pub type NodeHash = [u8; 32];

/// A Node of a B+Tree, parameterized by `MAX` (maximum number of children).
///
/// The default `MAX` is [`DEFAULT_MAX_CHILDREN`] (20, i.e. order 10).
///
/// The keys are sorted in ascending order.
/// The keys partition the children: keys greater or equal go right.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Node<K, NR, const MAX: usize = DEFAULT_MAX_CHILDREN> {
    pub keys: ArrayVec<K, MAX>,
    pub children: ArrayVec<NR, MAX>,
}

/// A lightweight, Copy index into a [`NodeArena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeRef {
    Inner(u32),
    Leaf(u32),
    Stored(Idx),
}

impl NodeRef {
    pub fn stored(self) -> Option<Idx> {
        match self {
            NodeRef::Stored(idx) => Some(idx),
            _ => None,
        }
    }
}

pub type InnerNode<K> = Node<K, NodeRef>;
pub type LeafNode<K, V> = Node<K, V>;

pub type InnerNodeSnapshot<K> = Node<K, Idx>;

// ---------------------------------------------------------------------------
// NodeArena
// ---------------------------------------------------------------------------

pub struct NodeArena<K, V> {
    pub(crate) inner_nodes: Slab<InnerNode<K>>,
    pub(crate) leaf_nodes: Slab<LeafNode<K, V>>,
}

impl<K, V> Default for NodeArena<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> NodeArena<K, V> {
    pub fn new() -> Self {
        Self {
            inner_nodes: Slab::new(),
            leaf_nodes: Slab::new(),
        }
    }

    #[inline]
    pub fn alloc_inner(&mut self, node: InnerNode<K>) -> u32 {
        self.inner_nodes.insert(node) as u32
    }

    #[inline]
    pub fn alloc_leaf(&mut self, node: LeafNode<K, V>) -> u32 {
        self.leaf_nodes.insert(node) as u32
    }

    #[inline]
    pub fn inner(&self, idx: u32) -> &InnerNode<K> {
        &self.inner_nodes[idx as usize]
    }

    #[inline]
    pub fn inner_mut(&mut self, idx: u32) -> &mut InnerNode<K> {
        &mut self.inner_nodes[idx as usize]
    }

    #[inline]
    pub fn leaf(&self, idx: u32) -> &LeafNode<K, V> {
        &self.leaf_nodes[idx as usize]
    }

    #[inline]
    pub fn leaf_mut(&mut self, idx: u32) -> &mut LeafNode<K, V> {
        &mut self.leaf_nodes[idx as usize]
    }
}

impl<K: Clone, V: Clone> NodeArena<K, V> {
    /// Load a stored node from the data store into the arena, returning a [`NodeRef`].
    pub fn load_stored<S>(
        &mut self,
        data_store: &S,
        stored_idx: Idx,
    ) -> Result<NodeRef, crate::errors::BTreeError>
    where
        S: crate::store::Store<Key = K, Value = V>,
    {
        let snapshot_node = data_store.get(stored_idx)?;
        Ok(match snapshot_node {
            InnerOuter::Inner(node) => {
                let inner = Node {
                    keys: node.keys.clone(),
                    children: node
                        .children
                        .iter()
                        .map(|&idx| NodeRef::Stored(idx))
                        .collect(),
                };
                NodeRef::Inner(self.alloc_inner(inner))
            }
            InnerOuter::Outer(leaf) => NodeRef::Leaf(self.alloc_leaf(leaf.clone())),
        })
    }
}

// ---------------------------------------------------------------------------
// Node common impl
// ---------------------------------------------------------------------------

impl<K, V, const MAX: usize> Node<K, V, MAX> {
    pub const fn is_full(&self) -> bool {
        self.children.len() == Self::max_children()
    }

    pub fn is_too_small(&self) -> bool {
        self.children.len() < Self::min_children()
    }

    pub const fn max_children() -> usize {
        MAX
    }

    pub const fn min_children() -> usize {
        MAX / 2
    }

    pub const fn max_inner_node_keys() -> usize {
        MAX - 1
    }

    pub const fn min_keys() -> usize {
        MAX / 2 - 1
    }

    #[track_caller]
    pub fn assert_keys_sorted(&self)
    where
        K: Ord,
    {
        for i in 1..self.keys.len() {
            assert!(self.keys[i - 1] < self.keys[i]);
        }
    }
}

impl<K: Ord> InnerNode<K> {
    #[track_caller]
    pub fn assert_inner_invariants(&self) {
        self.assert_keys_sorted();
        assert_eq!(self.keys.len(), self.children.len() - 1);
    }
}

impl<K: Ord, V> LeafNode<K, V> {
    #[track_caller]
    pub fn assert_leaf_invariants(&self) {
        self.assert_keys_sorted();
        assert_eq!(self.keys.len(), self.children.len());
    }
}

// ---------------------------------------------------------------------------
// Leaf split (operates on a single node, returns the new sibling by value)
// ---------------------------------------------------------------------------

impl<K: Clone + Ord, V> LeafNode<K, V> {
    pub(crate) fn insert_split(&mut self, idx: usize, key: K, value: V) -> (K, Self) {
        #[cfg(debug_assertions)]
        self.assert_leaf_invariants();

        let mut new_right = Node {
            keys: self.keys.drain(Self::min_children()..).collect(),
            children: self.children.drain(Self::min_children()..).collect(),
        };

        if idx < Self::min_children() {
            self.keys.insert(idx, key);
            self.children.insert(idx, value);
        } else {
            let adjusted = idx - Self::min_children();
            new_right.keys.insert(adjusted, key);
            new_right.children.insert(adjusted, value);
        }

        let middle_key = self.keys.last().unwrap().clone();

        #[cfg(debug_assertions)]
        {
            self.assert_leaf_invariants();
            new_right.assert_leaf_invariants();
        }

        (middle_key, new_right)
    }
}

// ---------------------------------------------------------------------------
// Inner split (needs arena for allocation)
// ---------------------------------------------------------------------------

pub(crate) fn handle_inner_split<K: Clone + Ord, V>(
    arena: &mut NodeArena<K, V>,
    parent_idx: u32,
    child_idx: usize,
    middle_key: K,
    new_right: NodeRef,
) -> InsertResult<K, V> {
    if !arena.inner(parent_idx).is_full() {
        let parent = arena.inner_mut(parent_idx);
        parent.keys.insert(child_idx, middle_key);
        parent.children.insert(child_idx + 1, new_right);
        return InsertResult::Inserted;
    }

    let (new_middle_key, new_right_inner) = {
        let parent = arena.inner_mut(parent_idx);
        let mut new_right_inner = Node {
            keys: parent
                .keys
                .drain((InnerNode::<K>::min_keys() + 1)..)
                .collect(),
            children: parent
                .children
                .drain(InnerNode::<K>::min_children()..)
                .collect(),
        };
        let new_middle_key = parent.keys.pop().unwrap();

        if child_idx < InnerNode::<K>::min_children() {
            parent.keys.insert(child_idx, middle_key);
            parent.children.insert(child_idx + 1, new_right);
        } else {
            let adjusted = child_idx - InnerNode::<K>::min_children();
            new_right_inner.keys.insert(adjusted, middle_key);
            new_right_inner.children.insert(adjusted + 1, new_right);
        }

        #[cfg(debug_assertions)]
        {
            parent.assert_inner_invariants();
            new_right_inner.assert_inner_invariants();
        }

        (new_middle_key, new_right_inner)
    };

    let right_idx = arena.alloc_inner(new_right_inner);
    InsertResult::Split {
        middle_key: new_middle_key,
        right_ref: NodeRef::Inner(right_idx),
    }
}

pub(crate) enum InsertResult<K, V> {
    Inserted,
    Replaced(V),
    Split { middle_key: K, right_ref: NodeRef },
}

// ---------------------------------------------------------------------------
// Merge / Balance (arena-aware free functions)
// ---------------------------------------------------------------------------

fn can_leaves_be_merged<K: Ord, V>(arena: &NodeArena<K, V>, a: u32, b: u32) -> bool {
    let la = &arena.leaf_nodes[a as usize];
    let lb = &arena.leaf_nodes[b as usize];
    #[cfg(debug_assertions)]
    if let ([.., left_last], [right_first, ..]) = (la.keys.as_slice(), lb.keys.as_slice()) {
        assert!(left_last < right_first);
    }
    la.children.len() + lb.children.len() <= LeafNode::<K, V>::max_children()
}

fn merge_leaves<K: Clone + Ord, V>(arena: &mut NodeArena<K, V>, left_idx: u32, right_idx: u32) {
    let rk: Vec<K> = arena.leaf_mut(right_idx).keys.drain(..).collect();
    let rc: Vec<V> = arena.leaf_mut(right_idx).children.drain(..).collect();
    let left = arena.leaf_mut(left_idx);
    left.keys.extend(rk);
    left.children.extend(rc);
    #[cfg(debug_assertions)]
    left.assert_leaf_invariants();
}

fn balance_leaves<K: Clone + Ord, V>(
    arena: &mut NodeArena<K, V>,
    left_idx: u32,
    right_idx: u32,
) -> K {
    let left_len = arena.leaf(left_idx).children.len();
    let right_len = arena.leaf(right_idx).children.len();
    let total = left_len + right_len;
    let target_left = total / 2;

    debug_assert!(total > LeafNode::<K, V>::max_children());

    if left_len < target_left {
        let to_steal = target_left - left_len;
        let sk: Vec<K> = arena.leaf_mut(right_idx).keys.drain(..to_steal).collect();
        let sc: Vec<V> = arena
            .leaf_mut(right_idx)
            .children
            .drain(..to_steal)
            .collect();
        let left = arena.leaf_mut(left_idx);
        left.keys.extend(sk);
        left.children.extend(sc);
    } else {
        let to_give = left_len - target_left;
        let start = left_len - to_give;
        let sk: Vec<K> = arena.leaf_mut(left_idx).keys.drain(start..).collect();
        let sc: Vec<V> = arena.leaf_mut(left_idx).children.drain(start..).collect();
        let right = arena.leaf_mut(right_idx);
        for (i, (k, v)) in sk.into_iter().zip(sc).enumerate() {
            right.keys.insert(i, k);
            right.children.insert(i, v);
        }
    }

    #[cfg(debug_assertions)]
    {
        arena.leaf(left_idx).assert_leaf_invariants();
        assert!(arena.leaf(left_idx).keys.len() >= LeafNode::<K, V>::min_keys());
        arena.leaf(right_idx).assert_leaf_invariants();
        assert!(arena.leaf(right_idx).keys.len() >= LeafNode::<K, V>::min_keys());
    }

    arena.leaf(left_idx).keys.last().unwrap().clone()
}

fn can_inner_be_merged<K: Ord, V>(arena: &NodeArena<K, V>, a: u32, b: u32) -> bool {
    let la = &arena.inner_nodes[a as usize];
    let lb = &arena.inner_nodes[b as usize];
    #[cfg(debug_assertions)]
    {
        match (la.keys.as_slice(), lb.keys.as_slice()) {
            ([.., left_last], [right_first, ..]) => assert!(left_last < right_first),
            ([], _) => assert!(la.children.len() == 1),
            (_, []) => assert!(lb.children.len() == 1),
        };
    }
    la.keys.len() + lb.keys.len() < InnerNode::<K>::max_inner_node_keys()
}

fn merge_inner<K: Clone + Ord, V>(
    arena: &mut NodeArena<K, V>,
    left_idx: u32,
    middle_key: K,
    right_idx: u32,
) {
    let rk: Vec<K> = arena.inner_mut(right_idx).keys.drain(..).collect();
    let rc: Vec<NodeRef> = arena.inner_mut(right_idx).children.drain(..).collect();
    let left = arena.inner_mut(left_idx);

    #[cfg(debug_assertions)]
    {
        let key_count = left.keys.len() + 1 + rk.len();
        let child_count = left.children.len() + rc.len();
        debug_assert_eq!(key_count, child_count - 1);
        debug_assert!(key_count <= InnerNode::<K>::max_inner_node_keys());
    }

    left.keys.push(middle_key);
    left.keys.extend(rk);
    left.children.extend(rc);

    #[cfg(debug_assertions)]
    left.assert_inner_invariants();
}

fn balance_inner<K: Clone + Ord, V>(
    arena: &mut NodeArena<K, V>,
    parent_idx: u32,
    parent_key_idx: usize,
    left_idx: u32,
    right_idx: u32,
) {
    let middle_key = arena.inner(parent_idx).keys[parent_key_idx].clone();

    let left_len = arena.inner(left_idx).children.len();
    let right_len = arena.inner(right_idx).children.len();
    let total_children = left_len + right_len;
    let target_left = total_children / 2;

    debug_assert!(left_len + right_len > InnerNode::<K>::max_children());

    // Drain everything, redistribute, write back.
    // Inner node balance is rare and the node size is small, so this is acceptable.
    let mut all_keys: Vec<K> = arena.inner_mut(left_idx).keys.drain(..).collect();
    all_keys.push(middle_key);
    all_keys.extend(arena.inner_mut(right_idx).keys.drain(..));

    let mut all_children: Vec<NodeRef> = arena.inner_mut(left_idx).children.drain(..).collect();
    all_children.extend(arena.inner_mut(right_idx).children.drain(..));

    let left = arena.inner_mut(left_idx);
    left.keys.extend(all_keys.drain(..target_left - 1));
    left.children.extend(all_children.drain(..target_left));

    let new_middle = all_keys.remove(0);

    let right = arena.inner_mut(right_idx);
    right.keys.extend(all_keys);
    right.children.extend(all_children);

    arena.inner_mut(parent_idx).keys[parent_key_idx] = new_middle;

    #[cfg(debug_assertions)]
    {
        arena.inner(left_idx).assert_inner_invariants();
        assert!(arena.inner(left_idx).keys.len() >= InnerNode::<K>::min_keys());
        arena.inner(right_idx).assert_inner_invariants();
        assert!(arena.inner(right_idx).keys.len() >= InnerNode::<K>::min_keys());
    }
}

/// Try to merge or balance a child that underflowed.
/// Returns `Err(())` when both siblings are `Stored` (caller must load one first).
#[allow(clippy::result_unit_err)]
pub(crate) fn merge_or_balance<K: Clone + Ord, V: Clone>(
    arena: &mut NodeArena<K, V>,
    parent_idx: u32,
    underflow_idx: usize,
) -> Result<(), ()> {
    let parent = arena.inner(parent_idx);
    let children_len = parent.children.len();
    debug_assert!(underflow_idx < children_len);

    let left_ref = if underflow_idx > 0 {
        Some(parent.children[underflow_idx - 1])
    } else {
        None
    };
    let under_ref = parent.children[underflow_idx];
    let right_ref = if underflow_idx + 1 < children_len {
        Some(parent.children[underflow_idx + 1])
    } else {
        None
    };
    // parent immutable borrow ends here (we only copied NodeRef values)

    // --- Leaf merges ---
    if let (Some(NodeRef::Leaf(li)), NodeRef::Leaf(ui)) = (left_ref, under_ref) {
        if can_leaves_be_merged(arena, li, ui) {
            merge_leaves(arena, li, ui);
            let p = arena.inner_mut(parent_idx);
            p.keys.remove(underflow_idx - 1);
            p.children.remove(underflow_idx);
            return Ok(());
        }
    }
    if let (NodeRef::Leaf(ui), Some(NodeRef::Leaf(ri))) = (under_ref, right_ref) {
        if can_leaves_be_merged(arena, ui, ri) {
            merge_leaves(arena, ui, ri);
            let p = arena.inner_mut(parent_idx);
            p.keys.remove(underflow_idx);
            p.children.remove(underflow_idx + 1);
            return Ok(());
        }
    }
    // --- Leaf balances ---
    if let (Some(NodeRef::Leaf(li)), NodeRef::Leaf(ui)) = (left_ref, under_ref) {
        let mk = balance_leaves(arena, li, ui);
        arena.inner_mut(parent_idx).keys[underflow_idx - 1] = mk;
        return Ok(());
    }
    if let (NodeRef::Leaf(ui), Some(NodeRef::Leaf(ri))) = (under_ref, right_ref) {
        let mk = balance_leaves(arena, ui, ri);
        arena.inner_mut(parent_idx).keys[underflow_idx] = mk;
        return Ok(());
    }
    // --- Inner merges ---
    if let (Some(NodeRef::Inner(li)), NodeRef::Inner(ui)) = (left_ref, under_ref) {
        if can_inner_be_merged(arena, li, ui) {
            let mk = arena.inner_mut(parent_idx).keys.remove(underflow_idx - 1);
            merge_inner(arena, li, mk, ui);
            arena.inner_mut(parent_idx).children.remove(underflow_idx);
            return Ok(());
        }
    }
    if let (NodeRef::Inner(ui), Some(NodeRef::Inner(ri))) = (under_ref, right_ref) {
        if can_inner_be_merged(arena, ui, ri) {
            let mk = arena.inner_mut(parent_idx).keys.remove(underflow_idx);
            merge_inner(arena, ui, mk, ri);
            arena
                .inner_mut(parent_idx)
                .children
                .remove(underflow_idx + 1);
            return Ok(());
        }
    }
    // --- Inner balances ---
    if let (Some(NodeRef::Inner(li)), NodeRef::Inner(ui)) = (left_ref, under_ref) {
        balance_inner(arena, parent_idx, underflow_idx - 1, li, ui);
        return Ok(());
    }
    if let (NodeRef::Inner(ui), Some(NodeRef::Inner(ri))) = (under_ref, right_ref) {
        balance_inner(arena, parent_idx, underflow_idx, ui, ri);
        return Ok(());
    }
    // --- Both siblings stored ---
    if matches!(
        (left_ref, right_ref),
        (Some(NodeRef::Stored(_)) | None, Some(NodeRef::Stored(_)))
            | (Some(NodeRef::Stored(_)), None)
    ) {
        return Err(());
    }

    unreachable!("An InnerNode should only have one type of children");
}

// ---------------------------------------------------------------------------
// PortableHash – Phase 3: includes length prefix
// ---------------------------------------------------------------------------

impl<K: PortableHash, V: PortableHash, const MAX: usize> PortableHash for Node<K, V, MAX> {
    fn portable_hash<H: PortableUpdate>(&self, hasher: &mut H) {
        (self.keys.len() as u32).portable_hash(hasher);
        (self.children.len() as u32).portable_hash(hasher);
        self.keys.iter().for_each(|key| key.portable_hash(hasher));
        self.children
            .iter()
            .for_each(|child| child.portable_hash(hasher));
    }
}

impl<K: PortableHash, NR, const MAX: usize> Node<K, NR, MAX> {
    /// Hash this node's keys together with externally-computed child hashes.
    /// The byte order matches [`PortableHash::portable_hash`] on `Node<K, NodeHash>`.
    pub fn portable_hash_iter<'l>(
        &self,
        hasher: &mut impl PortableUpdate,
        child_hashes: &[NodeHash],
    ) {
        (self.keys.len() as u32).portable_hash(hasher);
        (child_hashes.len() as u32).portable_hash(hasher);
        self.keys.iter().for_each(|key| key.portable_hash(hasher));
        child_hashes.iter().for_each(|h| h.portable_hash(hasher));
    }
}

// ---------------------------------------------------------------------------
// InnerOuter enum
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InnerOuter<N, L> {
    Inner(N),
    Outer(L),
}

impl<N, L> InnerOuter<N, L> {
    pub fn node(&self) -> Option<&N> {
        match self {
            InnerOuter::Inner(n) => Some(n),
            _ => None,
        }
    }

    pub fn leaf(&self) -> Option<&L> {
        match self {
            InnerOuter::Outer(l) => Some(l),
            _ => None,
        }
    }
}

pub type NodeOrLeafDb<K, V> = InnerOuter<Node<K, NodeHash>, LeafNode<K, V>>;
pub type InnerOuterSnapshotRef<'a, K, V> = InnerOuter<&'a InnerNodeSnapshot<K>, &'a LeafNode<K, V>>;
pub type InnerOuterSnapshotOwned<K, V> = InnerOuter<InnerNodeSnapshot<K>, LeafNode<K, V>>;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::hash::{DigestHasher, PortableHasher};
    use proptest::prelude::*;
    use sha2::Sha256;

    proptest! {
        #[test]
        fn test_portable_hash_matches(
            keys in proptest::collection::vec(0u32..100, 1..(BTREE_ORDER * 2 - 1)),
            child_hashes in proptest::collection::vec(any::<[u8; 32]>(), 2..(BTREE_ORDER * 2)),
        ) {
            let node_with_hashes: Node<u32, [u8; 32]> = Node {
                keys: ArrayVec::from_iter(keys.clone()),
                children: ArrayVec::from_iter(child_hashes.clone()),
            };

            let hasher1 = &mut DigestHasher::<Sha256>::default();
            let hasher2 = &mut DigestHasher::<Sha256>::default();

            node_with_hashes.portable_hash(hasher1);
            node_with_hashes.portable_hash_iter(hasher2, &child_hashes);

            assert_eq!(hasher1.finalize_reset(), hasher2.finalize_reset());
        }
    }

    #[test]
    fn arena_alloc_returns_sequential_indices() {
        let mut arena = NodeArena::<u32, u32>::new();
        let i0 = arena.alloc_leaf(Node {
            keys: ArrayVec::from_iter([1]),
            children: ArrayVec::from_iter([10]),
        });
        let i1 = arena.alloc_leaf(Node {
            keys: ArrayVec::from_iter([2]),
            children: ArrayVec::from_iter([20]),
        });
        assert_eq!(i0, 0);
        assert_eq!(i1, 1);
        assert_eq!(arena.leaf(i0).keys[0], 1);
        assert_eq!(arena.leaf(i1).children[0], 20);
    }

    #[test]
    fn arena_inner_mut_does_not_affect_other_nodes() {
        let mut arena = NodeArena::<u32, u32>::new();
        let leaf0 = arena.alloc_leaf(Node {
            keys: ArrayVec::from_iter([1, 2]),
            children: ArrayVec::from_iter([10, 20]),
        });
        let leaf1 = arena.alloc_leaf(Node {
            keys: ArrayVec::from_iter([3, 4]),
            children: ArrayVec::from_iter([30, 40]),
        });
        arena.leaf_mut(leaf0).keys[0] = 99;
        assert_eq!(arena.leaf(leaf0).keys[0], 99);
        assert_eq!(arena.leaf(leaf1).keys[0], 3);
    }
}
