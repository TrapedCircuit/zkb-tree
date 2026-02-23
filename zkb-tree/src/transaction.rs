use core::mem;
use smallvec::SmallVec;
use core::{
    borrow::Borrow,
    marker::PhantomData,
    ops::{Bound, RangeBounds, RangeFull},
};

use crate::hash::{PortableHash, PortableHasher};
use arrayvec::ArrayVec;

use crate::{
    db::{DatabaseGet, DatabaseSet},
    errors::BTreeError,
    node::{
        handle_inner_split, merge_or_balance, InnerNode, InnerNodeSnapshot, InnerOuter,
        InsertResult, LeafNode, Node, NodeArena, NodeHash, NodeRef, DEFAULT_MAX_CHILDREN,
        EMPTY_TREE_ROOT_HASH,
    },
    snapshot::{Snapshot, SnapshotBuilder, VerifiedSnapshot},
    store::{Idx, Store},
};

/// A transaction against a merkle b+tree.
pub struct Transaction<S: Store> {
    pub data_store: S,
    pub(crate) arena: NodeArena<S::Key, S::Value>,
    current_root: Option<NodeRef>,
}

impl<S: Store> Transaction<S> {
    pub fn new(data_store: S) -> Self {
        let root = data_store.get_store_root_idx().map(NodeRef::Stored);
        Self {
            arena: NodeArena::new(),
            current_root: root,
            data_store,
        }
    }

    // -----------------------------------------------------------------------
    // calc_root_hash
    // -----------------------------------------------------------------------

    #[inline]
    pub fn calc_root_hash(
        &self,
        hasher: &mut impl PortableHasher<32>,
    ) -> Result<NodeHash, BTreeError> {
        self.calc_root_hash_inner(hasher, &mut |_, _| Ok(()), &mut |_, _, _| Ok(()))
    }

    fn calc_root_hash_inner(
        &self,
        hasher: &mut impl PortableHasher<32>,
        on_modified_leaf: &mut impl FnMut(
            &NodeHash,
            &LeafNode<S::Key, S::Value>,
        ) -> Result<(), BTreeError>,
        on_modified_branch: &mut impl FnMut(
            &NodeHash,
            &InnerNode<S::Key>,
            &ArrayVec<NodeHash, DEFAULT_MAX_CHILDREN>,
        ) -> Result<(), BTreeError>,
    ) -> Result<NodeHash, BTreeError> {
        match self.current_root {
            None => Ok(EMPTY_TREE_ROOT_HASH),
            Some(NodeRef::Leaf(li)) if self.arena.leaf(li).keys.is_empty() => {
                Ok(EMPTY_TREE_ROOT_HASH)
            }
            Some(node_ref) => self.calc_hash_node(
                #[cfg(debug_assertions)]
                0,
                hasher,
                node_ref,
                on_modified_leaf,
                on_modified_branch,
            ),
        }
    }

    fn calc_hash_node(
        &self,
        #[cfg(debug_assertions)] depth: usize,
        hasher: &mut impl PortableHasher<32>,
        node_ref: NodeRef,
        on_modified_leaf: &mut impl FnMut(
            &NodeHash,
            &LeafNode<S::Key, S::Value>,
        ) -> Result<(), BTreeError>,
        on_modified_branch: &mut impl FnMut(
            &NodeHash,
            &InnerNode<S::Key>,
            &ArrayVec<NodeHash, DEFAULT_MAX_CHILDREN>,
        ) -> Result<(), BTreeError>,
    ) -> Result<NodeHash, BTreeError> {
        match node_ref {
            NodeRef::Inner(ii) => {
                let node = self.arena.inner(ii);
                #[cfg(debug_assertions)]
                {
                    node.assert_inner_invariants();
                    debug_assert!(
                        depth == 0 || node.children.len() >= InnerNode::<S::Key>::min_children()
                    );
                }

                let mut child_hashes = ArrayVec::<NodeHash, DEFAULT_MAX_CHILDREN>::new();
                for &child_ref in &node.children {
                    let h = self.calc_hash_node(
                        #[cfg(debug_assertions)]
                        (depth + 1),
                        hasher,
                        child_ref,
                        on_modified_leaf,
                        on_modified_branch,
                    )?;
                    child_hashes.push(h);
                }

                let node = self.arena.inner(ii);
                node.portable_hash_iter(hasher, &child_hashes);
                let hash = hasher.finalize_reset();
                on_modified_branch(&hash, node, &child_hashes)?;
                Ok(hash)
            }
            NodeRef::Leaf(li) => {
                let leaf = self.arena.leaf(li);
                #[cfg(debug_assertions)]
                {
                    leaf.assert_leaf_invariants();
                    debug_assert!(
                        depth == 0
                            || leaf.children.len() >= Node::<S::Key, S::Value>::min_children()
                    );
                }
                leaf.portable_hash(hasher);
                let hash = hasher.finalize_reset();
                on_modified_leaf(&hash, leaf)?;
                Ok(hash)
            }
            NodeRef::Stored(si) => self.data_store.calc_subtree_hash(hasher, si),
        }
    }

    // -----------------------------------------------------------------------
    // get
    // -----------------------------------------------------------------------

    pub fn get(&self, key: &S::Key) -> Result<Option<&S::Value>, BTreeError> {
        match self.current_root {
            None => Ok(None),
            Some(NodeRef::Inner(ii)) => self.get_inner(ii, key),
            Some(NodeRef::Leaf(li)) => {
                let leaf = self.arena.leaf(li);
                match leaf.keys.binary_search(key) {
                    Ok(i) => Ok(Some(&leaf.children[i])),
                    Err(_) => Ok(None),
                }
            }
            Some(NodeRef::Stored(si)) => Self::get_stored(&self.data_store, si, key),
        }
    }

    fn get_inner(&self, mut inner_idx: u32, key: &S::Key) -> Result<Option<&S::Value>, BTreeError> {
        loop {
            let node = self.arena.inner(inner_idx);
            let idx = match node.keys.binary_search(key) {
                Ok(i) | Err(i) => i,
            };
            match node.children[idx] {
                NodeRef::Inner(ci) => inner_idx = ci,
                NodeRef::Leaf(li) => {
                    let leaf = self.arena.leaf(li);
                    return match leaf.keys.binary_search(key) {
                        Ok(i) => Ok(Some(&leaf.children[i])),
                        Err(_) => Ok(None),
                    };
                }
                NodeRef::Stored(si) => return Self::get_stored(&self.data_store, si, key),
            }
        }
    }

    fn get_stored<'s>(
        data_store: &'s S,
        mut stored_idx: Idx,
        key: &S::Key,
    ) -> Result<Option<&'s S::Value>, BTreeError> {
        loop {
            let node = data_store.get(stored_idx)?;
            match node {
                InnerOuter::Inner(n) => {
                    let idx = match n.keys.binary_search(key) {
                        Ok(i) | Err(i) => i,
                    };
                    stored_idx = n.children[idx];
                }
                InnerOuter::Outer(leaf) => {
                    return match leaf.keys.binary_search(key) {
                        Ok(i) => Ok(Some(&leaf.children[i])),
                        Err(_) => Ok(None),
                    };
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // insert
    // -----------------------------------------------------------------------

    pub fn insert(&mut self, key: S::Key, value: S::Value) -> Result<Option<S::Value>, BTreeError> {
        let split_result: (S::Key, NodeRef) = 'handle_split: {
            match self.current_root {
                None => {
                    let li = self.arena.alloc_leaf(Node {
                        keys: ArrayVec::from_iter([key]),
                        children: ArrayVec::from_iter([value]),
                    });
                    self.current_root = Some(NodeRef::Leaf(li));
                    return Ok(None);
                }
                Some(NodeRef::Stored(si)) => {
                    let loaded = self.arena.load_stored(&self.data_store, si)?;
                    self.current_root = Some(loaded);
                    return self.insert(key, value);
                }
                Some(NodeRef::Inner(ii)) => {
                    match Self::insert_inner(&mut self.arena, &self.data_store, ii, key, value)? {
                        InsertResult::Inserted => return Ok(None),
                        InsertResult::Replaced(old) => return Ok(Some(old)),
                        InsertResult::Split {
                            middle_key,
                            right_ref,
                        } => {
                            break 'handle_split (middle_key, right_ref);
                        }
                    }
                }
                Some(NodeRef::Leaf(li)) => {
                    let leaf = self.arena.leaf_mut(li);
                    match leaf.keys.binary_search(&key) {
                        Ok(i) => return Ok(Some(mem::replace(&mut leaf.children[i], value))),
                        Err(i) if !leaf.is_full() => {
                            leaf.keys.insert(i, key);
                            leaf.children.insert(i, value);
                            return Ok(None);
                        }
                        Err(i) => {
                            let (mk, new_right) = leaf.insert_split(i, key, value);
                            let ri = self.arena.alloc_leaf(new_right);
                            break 'handle_split (mk, NodeRef::Leaf(ri));
                        }
                    }
                }
            }
        };

        let (middle_key, new_right) = split_result;
        let old_root = self.current_root.unwrap();
        let new_root = self.arena.alloc_inner(InnerNode {
            keys: ArrayVec::from_iter([middle_key]),
            children: ArrayVec::from_iter([old_root, new_right]),
        });
        self.current_root = Some(NodeRef::Inner(new_root));

        #[cfg(debug_assertions)]
        self.arena.inner(new_root).assert_inner_invariants();

        Ok(None)
    }

    fn insert_inner(
        arena: &mut NodeArena<S::Key, S::Value>,
        data_store: &S,
        parent_idx: u32,
        key: S::Key,
        value: S::Value,
    ) -> Result<InsertResult<S::Key, S::Value>, BTreeError> {
        let idx = {
            let parent = arena.inner(parent_idx);
            debug_assert!(parent.keys.len() == parent.children.len() - 1);
            match parent.keys.binary_search(&key) {
                Ok(i) | Err(i) => i,
            }
        };

        'handle_stored: loop {
            let child_ref = arena.inner(parent_idx).children[idx];
            let (middle_key, new_right): (S::Key, NodeRef) = 'handle_split: {
                match child_ref {
                    NodeRef::Stored(si) => {
                        let loaded = arena.load_stored(data_store, si)?;
                        arena.inner_mut(parent_idx).children[idx] = loaded;
                        continue 'handle_stored;
                    }
                    NodeRef::Inner(ci) => {
                        match Self::insert_inner(arena, data_store, ci, key, value)? {
                            InsertResult::Split {
                                middle_key,
                                right_ref,
                            } => {
                                break 'handle_split (middle_key, right_ref);
                            }
                            r => return Ok(r),
                        }
                    }
                    NodeRef::Leaf(li) => {
                        let leaf = arena.leaf_mut(li);
                        match leaf.keys.binary_search(&key) {
                            Ok(i) => {
                                return Ok(InsertResult::Replaced(mem::replace(
                                    &mut leaf.children[i],
                                    value,
                                )));
                            }
                            Err(i) => {
                                if !leaf.is_full() {
                                    leaf.keys.insert(i, key);
                                    leaf.children.insert(i, value);
                                    return Ok(InsertResult::Inserted);
                                } else {
                                    let (mk, new_right) = leaf.insert_split(i, key, value);
                                    let ri = arena.alloc_leaf(new_right);
                                    break 'handle_split (mk, NodeRef::Leaf(ri));
                                }
                            }
                        }
                    }
                }
            };

            return Ok(handle_inner_split(
                arena, parent_idx, idx, middle_key, new_right,
            ));
        }
    }

    // -----------------------------------------------------------------------
    // remove
    // -----------------------------------------------------------------------

    pub fn remove(&mut self, key: &S::Key) -> Result<Option<S::Value>, BTreeError> {
        match self.current_root {
            None => Ok(None),
            Some(NodeRef::Stored(si)) => {
                let loaded = self.arena.load_stored(&self.data_store, si)?;
                self.current_root = Some(loaded);
                self.remove(key)
            }
            Some(NodeRef::Inner(ii)) => {
                match Self::remove_inner(&mut self.arena, &self.data_store, ii, key)? {
                    Remove::NotPresent => Ok(None),
                    Remove::Removed(v) => Ok(Some(v)),
                    Remove::Underflow(v) => {
                        let node = self.arena.inner(ii);
                        if node.keys.is_empty() {
                            debug_assert!(node.children.len() == 1);
                            self.current_root = Some(node.children[0]);
                        }
                        Ok(Some(v))
                    }
                }
            }
            Some(NodeRef::Leaf(li)) => {
                let leaf = self.arena.leaf_mut(li);
                match leaf.keys.binary_search(key) {
                    Ok(i) => {
                        let v = leaf.children.remove(i);
                        leaf.keys.remove(i);
                        Ok(Some(v))
                    }
                    Err(_) => Ok(None),
                }
            }
        }
    }

    fn remove_inner(
        arena: &mut NodeArena<S::Key, S::Value>,
        data_store: &S,
        parent_idx: u32,
        key: &S::Key,
    ) -> Result<Remove<S>, BTreeError> {
        let idx = {
            let parent = arena.inner(parent_idx);
            debug_assert!(parent.keys.len() == parent.children.len() - 1);
            match parent.keys.binary_search(key) {
                Ok(i) | Err(i) => i,
            }
        };

        let child_ref = arena.inner(parent_idx).children[idx];

        match child_ref {
            NodeRef::Inner(ci) => match Self::remove_inner(arena, data_store, ci, key)? {
                Remove::NotPresent => Ok(Remove::NotPresent),
                Remove::Removed(v) => Ok(Remove::Removed(v)),
                Remove::Underflow(v) => {
                    Self::handle_underflow(arena, data_store, parent_idx, idx, v)
                }
            },
            NodeRef::Leaf(li) => {
                let leaf = arena.leaf_mut(li);
                match leaf.keys.binary_search(key) {
                    Ok(leaf_idx) => {
                        let v = leaf.children.remove(leaf_idx);
                        leaf.keys.remove(leaf_idx);
                        if leaf.children.len() < Node::<S::Key, S::Value>::min_children() {
                            Self::handle_underflow(arena, data_store, parent_idx, idx, v)
                        } else {
                            Ok(Remove::Removed(v))
                        }
                    }
                    Err(_) => Ok(Remove::NotPresent),
                }
            }
            NodeRef::Stored(si) => {
                let loaded = arena.load_stored(data_store, si)?;
                arena.inner_mut(parent_idx).children[idx] = loaded;
                Self::remove_inner(arena, data_store, parent_idx, key)
            }
        }
    }

    fn handle_underflow(
        arena: &mut NodeArena<S::Key, S::Value>,
        data_store: &S,
        parent_idx: u32,
        idx: usize,
        value: S::Value,
    ) -> Result<Remove<S>, BTreeError> {
        if let Err(()) = merge_or_balance(arena, parent_idx, idx) {
            // Both siblings are stored; load one.
            if idx == 0 {
                let si = arena.inner(parent_idx).children[1].stored().unwrap();
                let loaded = arena.load_stored(data_store, si)?;
                arena.inner_mut(parent_idx).children[1] = loaded;
            } else {
                let si = arena.inner(parent_idx).children[idx - 1].stored().unwrap();
                let loaded = arena.load_stored(data_store, si)?;
                arena.inner_mut(parent_idx).children[idx - 1] = loaded;
            }
            merge_or_balance(arena, parent_idx, idx).unwrap();
        }

        if arena.inner(parent_idx).is_too_small() {
            Ok(Remove::Underflow(value))
        } else {
            Ok(Remove::Removed(value))
        }
    }

    // -----------------------------------------------------------------------
    // first_key_value / last_key_value
    // -----------------------------------------------------------------------

    pub fn first_key_value(&self) -> Result<Option<(&S::Key, &S::Value)>, BTreeError> {
        match self.current_root {
            None => Ok(None),
            Some(NodeRef::Inner(ii)) => {
                let mut node = self.arena.inner(ii);
                loop {
                    match node.children[0] {
                        NodeRef::Inner(ci) => node = self.arena.inner(ci),
                        NodeRef::Leaf(li) => {
                            let l = self.arena.leaf(li);
                            return Ok(Some((&l.keys[0], &l.children[0])));
                        }
                        NodeRef::Stored(si) => return self.first_key_value_stored(si),
                    }
                }
            }
            Some(NodeRef::Leaf(li)) => {
                let l = self.arena.leaf(li);
                if l.keys.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some((&l.keys[0], &l.children[0])))
                }
            }
            Some(NodeRef::Stored(si)) => self.first_key_value_stored(si),
        }
    }

    fn first_key_value_stored(
        &self,
        mut si: Idx,
    ) -> Result<Option<(&S::Key, &S::Value)>, BTreeError> {
        loop {
            match self.data_store.get(si)? {
                InnerOuter::Inner(n) => si = n.children[0],
                InnerOuter::Outer(l) => return Ok(Some((&l.keys[0], &l.children[0]))),
            }
        }
    }

    pub fn last_key_value(&self) -> Result<Option<(&S::Key, &S::Value)>, BTreeError> {
        match self.current_root {
            None => Ok(None),
            Some(NodeRef::Inner(ii)) => {
                let mut node = self.arena.inner(ii);
                loop {
                    match *node.children.last().unwrap() {
                        NodeRef::Inner(ci) => node = self.arena.inner(ci),
                        NodeRef::Leaf(li) => {
                            let l = self.arena.leaf(li);
                            return Ok(Some((l.keys.last().unwrap(), l.children.last().unwrap())));
                        }
                        NodeRef::Stored(si) => return self.last_key_value_stored(si),
                    }
                }
            }
            Some(NodeRef::Leaf(li)) => {
                let l = self.arena.leaf(li);
                if l.keys.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some((l.keys.last().unwrap(), l.children.last().unwrap())))
                }
            }
            Some(NodeRef::Stored(si)) => self.last_key_value_stored(si),
        }
    }

    fn last_key_value_stored(
        &self,
        mut si: Idx,
    ) -> Result<Option<(&S::Key, &S::Value)>, BTreeError> {
        loop {
            match self.data_store.get(si)? {
                InnerOuter::Inner(n) => si = *n.children.last().unwrap(),
                InnerOuter::Outer(l) => {
                    return Ok(Some((l.keys.last().unwrap(), l.children.last().unwrap())));
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // range / iter
    // -----------------------------------------------------------------------

    pub fn range<K, R>(&self, range: R) -> Range<'_, S, K, R>
    where
        R: RangeBounds<K>,
        K: Borrow<S::Key>,
    {
        Range {
            txn: self,
            range,
            stack: SmallVec::new(),
            current_leaf: None,
            phantom: PhantomData,
        }
    }

    pub fn iter(&self) -> Iter<'_, S> {
        Iter {
            range: self.range(..),
        }
    }
}

// ---------------------------------------------------------------------------
// SnapshotBuilder transaction constructors
// ---------------------------------------------------------------------------

impl<K: Ord + Clone + PortableHash, V: Clone + PortableHash, Db: DatabaseGet<K, V>>
    Transaction<SnapshotBuilder<K, V, Db>>
{
    pub fn new_snapshot_builder_txn(root: NodeHash, db: Db) -> Self {
        debug_assert!(EMPTY_TREE_ROOT_HASH == NodeHash::default());
        if root == EMPTY_TREE_ROOT_HASH {
            Self {
                data_store: SnapshotBuilder::new(root, db),
                arena: NodeArena::new(),
                current_root: None,
            }
        } else {
            Self {
                data_store: SnapshotBuilder::new(root, db),
                arena: NodeArena::new(),
                current_root: Some(NodeRef::Stored(0)),
            }
        }
    }

    #[inline]
    pub fn build_initial_snapshot(&self) -> Snapshot<K, V> {
        self.data_store.build_initial_snapshot()
    }
}

impl<'s, S: Store + AsRef<Snapshot<S::Key, S::Value>>> Transaction<&'s VerifiedSnapshot<S>> {
    #[inline]
    pub fn from_verified_snapshot_ref(snapshot: &'s VerifiedSnapshot<S>) -> Self {
        Transaction {
            current_root: snapshot.root_node_ref(),
            arena: NodeArena::new(),
            data_store: snapshot,
        }
    }
}

impl<S: Store + AsRef<Snapshot<S::Key, S::Value>>> Transaction<VerifiedSnapshot<S>> {
    #[inline]
    pub fn from_verified_snapshot_owned(snapshot: VerifiedSnapshot<S>) -> Self {
        let root = snapshot.root_node_ref();
        Self {
            current_root: root,
            arena: NodeArena::new(),
            data_store: snapshot,
        }
    }
}

impl<K: Clone + PortableHash + Ord, V: Clone + PortableHash, Db: DatabaseSet<K, V>>
    Transaction<SnapshotBuilder<K, V, Db>>
{
    #[inline]
    pub fn from_snapshot_builder(snapshot_builder: SnapshotBuilder<K, V, Db>) -> Self {
        Self {
            current_root: Some(NodeRef::Stored(0)),
            arena: NodeArena::new(),
            data_store: snapshot_builder,
        }
    }

    #[inline]
    pub fn commit(&self, hasher: &mut impl PortableHasher<32>) -> Result<NodeHash, BTreeError> {
        let on_modified_leaf = &mut |hash: &NodeHash, leaf: &LeafNode<K, V>| {
            self.data_store
                .db
                .set(hash, InnerOuter::Outer(leaf.clone()))
                .map_err(|e| BTreeError::from(e.to_string()))
        };

        let on_modified_branch =
            &mut |hash: &NodeHash,
                  node: &InnerNode<K>,
                  child_hashes: &ArrayVec<_, DEFAULT_MAX_CHILDREN>| {
                let db_node = InnerOuter::Inner(Node {
                    keys: node.keys.clone(),
                    children: ArrayVec::from_iter(child_hashes.iter().cloned()),
                });
                self.data_store
                    .db
                    .set(hash, db_node)
                    .map_err(|e| BTreeError::from(e.to_string()))
            };

        self.calc_root_hash_inner(hasher, on_modified_leaf, on_modified_branch)
    }
}

// ---------------------------------------------------------------------------
// Remove enum
// ---------------------------------------------------------------------------

pub(crate) enum Remove<S: Store> {
    NotPresent,
    Removed(S::Value),
    Underflow(S::Value),
}

// ---------------------------------------------------------------------------
// Iterators
// ---------------------------------------------------------------------------

pub struct Iter<'s, S: Store> {
    range: Range<'s, S, S::Key, RangeFull>,
}

impl<'s, S: Store> Iterator for Iter<'s, S> {
    type Item = Result<(&'s S::Key, &'s S::Value), BTreeError>;
    fn next(&mut self) -> Option<Self::Item> {
        self.range.next()
    }
}

enum StackItem<'s, S: Store> {
    Arena(u32),
    Stored(&'s InnerNodeSnapshot<S::Key>),
}

pub struct Range<'s, S: Store, K: Borrow<S::Key>, R: RangeBounds<K>> {
    txn: &'s Transaction<S>,
    range: R,
    stack: SmallVec<[(usize, StackItem<'s, S>); 32]>,
    current_leaf: Option<(usize, &'s LeafNode<S::Key, S::Value>)>,
    phantom: PhantomData<K>,
}

#[allow(clippy::needless_lifetimes)]
impl<'s, S: Store, K: Borrow<S::Key>, R: RangeBounds<K>> Range<'s, S, K, R> {
    fn bound_to_idx<V>(&self, node: &Node<S::Key, V>) -> usize {
        match self.range.start_bound() {
            Bound::Included(key) => node.keys.binary_search(key.borrow()).unwrap_or_else(|i| i),
            Bound::Excluded(key) => match node.keys.binary_search(key.borrow()) {
                Ok(i) => i + 1,
                Err(i) => i,
            },
            Bound::Unbounded => 0,
        }
    }

    fn setup_stack(&mut self) -> Result<(), BTreeError> {
        debug_assert!(self.stack.is_empty());
        debug_assert!(self.current_leaf.is_none());

        match self.txn.current_root {
            None => Ok(()),
            Some(NodeRef::Inner(ii)) => {
                let mut cur = ii;
                loop {
                    let node = self.txn.arena.inner(cur);
                    let idx = self.bound_to_idx(node);
                    self.stack.push((idx, StackItem::Arena(cur)));
                    match node.children[idx] {
                        NodeRef::Inner(ci) => cur = ci,
                        NodeRef::Leaf(li) => {
                            let leaf = self.txn.arena.leaf(li);
                            let i = self.bound_to_idx(leaf);
                            self.current_leaf = Some((i, leaf));
                            return Ok(());
                        }
                        NodeRef::Stored(si) => return self.setup_stack_stored(si),
                    }
                }
            }
            Some(NodeRef::Leaf(li)) => {
                let leaf = self.txn.arena.leaf(li);
                let i = self.bound_to_idx(leaf);
                self.current_leaf = Some((i, leaf));
                Ok(())
            }
            Some(NodeRef::Stored(si)) => self.setup_stack_stored(si),
        }
    }

    fn setup_stack_stored(&mut self, mut si: Idx) -> Result<(), BTreeError> {
        loop {
            let node = self
                .txn
                .data_store
                .get(si)
                .map_err(|e| BTreeError::from(e.to_string()))?;
            match node {
                InnerOuter::Inner(n) => {
                    let idx = self.bound_to_idx(n);
                    self.stack.push((idx, StackItem::Stored(n)));
                    si = n.children[idx];
                }
                InnerOuter::Outer(leaf) => {
                    let i = self.bound_to_idx(leaf);
                    self.current_leaf = Some((i, leaf));
                    return Ok(());
                }
            }
        }
    }
}

impl<'s, S: Store, K: Borrow<S::Key>, R: RangeBounds<K>> Iterator for Range<'s, S, K, R> {
    type Item = Result<(&'s S::Key, &'s S::Value), BTreeError>;

    #[allow(clippy::question_mark)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.txn.current_root.is_none() {
            return None;
        }

        if self.current_leaf.is_none() {
            match (self.range.start_bound(), self.range.end_bound()) {
                (Bound::Included(s), Bound::Included(e)) if s.borrow() > e.borrow() => return None,
                (Bound::Excluded(s), Bound::Excluded(e)) if s.borrow() >= e.borrow() => {
                    return None
                }
                _ => {}
            }
            if let Err(e) = self.setup_stack() {
                return Some(Err(e));
            }
        }

        let (idx, leaf) = self.current_leaf.as_mut().unwrap();
        if let Some(child_key) = leaf.keys.get(*idx) {
            let in_range = match self.range.end_bound() {
                Bound::Included(key) => child_key <= key.borrow(),
                Bound::Excluded(key) => child_key < key.borrow(),
                Bound::Unbounded => true,
            };
            if in_range {
                let child = &leaf.children[*idx];
                *idx += 1;
                return Some(Ok((child_key, child)));
            } else {
                return None;
            }
        }

        // Leaf exhausted, pop stack
        loop {
            let Some((parent_idx, item)) = self.stack.last_mut() else {
                return None;
            };
            let children_len = match item {
                StackItem::Arena(ii) => self.txn.arena.inner(*ii).children.len(),
                StackItem::Stored(n) => n.children.len(),
            };
            if *parent_idx + 1 == children_len {
                self.stack.pop();
                continue;
            } else {
                *parent_idx += 1;
                break;
            }
        }

        // Descend into next child
        loop {
            let Some(&(parent_idx, ref item)) = self.stack.last() else {
                return None;
            };
            match item {
                StackItem::Arena(ii) => {
                    let node = self.txn.arena.inner(*ii);
                    match node.children[parent_idx] {
                        NodeRef::Inner(ci) => {
                            self.stack.push((0, StackItem::Arena(ci)));
                        }
                        NodeRef::Leaf(li) => {
                            self.current_leaf = Some((0, self.txn.arena.leaf(li)));
                            return self.next();
                        }
                        NodeRef::Stored(si) => match self.txn.data_store.get(si) {
                            Ok(InnerOuter::Inner(n)) => {
                                self.stack.push((0, StackItem::Stored(n)));
                            }
                            Ok(InnerOuter::Outer(l)) => {
                                self.current_leaf = Some((0, l));
                                return self.next();
                            }
                            Err(e) => return Some(Err(BTreeError::from(e.to_string()))),
                        },
                    }
                }
                StackItem::Stored(n) => {
                    let child_idx = n.children[parent_idx];
                    match self.txn.data_store.get(child_idx) {
                        Ok(InnerOuter::Inner(n)) => {
                            self.stack.push((0, StackItem::Stored(n)));
                        }
                        Ok(InnerOuter::Outer(l)) => {
                            self.current_leaf = Some((0, l));
                            return self.next();
                        }
                        Err(e) => return Some(Err(BTreeError::from(e.to_string()))),
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use crate::{db::MemoryDb, transaction::Transaction, Store};
    use alloc::collections::btree_map::BTreeMap;
    use proptest::prelude::*;
    use core::ops::RangeBounds;

    #[derive(Clone, Debug)]
    enum Op {
        Insert(u32, u32),
        Get(u32),
        Delete(u32),
        GetFirstKeyValue,
        GetLastKeyValue,
        IterAll,
        IterRange(Option<u32>, Option<u32>),
    }

    fn iter_test<S: Store<Key = u32, Value = u32>>(
        range: impl RangeBounds<u32> + Clone,
        txn: &Transaction<S>,
        std: &BTreeMap<u32, u32>,
    ) {
        let mut txn_iter = txn.range(range.clone()).enumerate();
        for res_std in std.range(range).enumerate() {
            let (i_txn, res_txn) = txn_iter.next().expect("too few elements");
            let res_txn = res_txn.expect("txn error");
            assert_eq!((i_txn, res_txn), res_std);
        }
    }

    fn run_operations(mut operations: Vec<Op>) {
        let mut txn_btree =
            Transaction::new_snapshot_builder_txn(Default::default(), MemoryDb::default());
        let mut std_btree = BTreeMap::new();
        operations.push(Op::IterAll);
        for op in operations {
            match op {
                Op::Insert(k, v) => {
                    let res_txn = txn_btree.insert(k, v).unwrap();
                    let res_std = std_btree.insert(k, v);
                    assert_eq!(res_txn, res_std);
                }
                Op::Get(k) => {
                    let res_txn = txn_btree.get(&k).unwrap().cloned();
                    let res_std = std_btree.get(&k).cloned();
                    assert_eq!(res_txn, res_std);
                }
                Op::Delete(k) => {
                    let res_txn = txn_btree.remove(&k).unwrap();
                    let res_std = std_btree.remove(&k);
                    assert_eq!(res_txn, res_std);
                }
                Op::GetFirstKeyValue => {
                    let res_txn = txn_btree.first_key_value().unwrap();
                    let res_std = std_btree.first_key_value();
                    assert_eq!(res_txn, res_std);
                }
                Op::GetLastKeyValue => {
                    let res_txn = txn_btree.last_key_value().unwrap();
                    let res_std = std_btree.last_key_value();
                    assert_eq!(res_txn, res_std);
                }
                Op::IterAll => {
                    let mut txn_iter = txn_btree.iter().enumerate();
                    for res_std in std_btree.iter().enumerate() {
                        let (i_txn, res_txn) = txn_iter.next().expect("too few elements");
                        let res_txn = res_txn.expect("txn error");
                        assert_eq!((i_txn, res_txn), res_std);
                    }
                }
                Op::IterRange(start, end) => {
                    if let (Some(s), Some(e)) = (start, end) {
                        if s > e {
                            assert!(txn_btree.range(s..e).next().is_none());
                            return;
                        }
                    }
                    match (start, end) {
                        (Some(s), Some(e)) => iter_test(s..e, &txn_btree, &std_btree),
                        (Some(s), None) => iter_test(s.., &txn_btree, &std_btree),
                        (None, Some(e)) => iter_test(..e, &txn_btree, &std_btree),
                        (None, None) => iter_test(.., &txn_btree, &std_btree),
                    };
                }
            }
        }
    }

    #[test]
    fn test_hardcoded_1_insert() {
        run_operations(vec![Op::Insert(0, 0), Op::Insert(1, 0), Op::Insert(2, 0)]);
    }

    #[test]
    fn test_hardcoded_5_insert_delete() {
        run_operations(vec![Op::Insert(0, 0), Op::Insert(1, 0), Op::Delete(1)]);
    }

    #[test]
    fn test_hardcoded_7_insert_delete() {
        run_operations(vec![
            Op::Insert(0, 0),
            Op::Insert(1, 0),
            Op::Insert(2, 0),
            Op::Insert(3, 0),
            Op::Insert(257, 0),
            Op::Insert(63, 0),
            Op::Insert(4, 0),
            Op::Insert(5, 0),
            Op::Insert(64, 0),
            Op::Insert(65, 0),
            Op::Insert(66, 0),
            Op::Insert(67, 0),
            Op::Insert(6, 0),
            Op::Delete(257),
        ]);
    }

    #[test]
    fn test_hardcoded_13_first_last() {
        run_operations(vec![
            Op::GetFirstKeyValue,
            Op::GetLastKeyValue,
            Op::Insert(100, 1),
            Op::GetFirstKeyValue,
            Op::GetLastKeyValue,
            Op::Insert(50, 2),
            Op::GetFirstKeyValue,
            Op::GetLastKeyValue,
            Op::Insert(150, 3),
            Op::GetFirstKeyValue,
            Op::GetLastKeyValue,
            Op::Delete(50),
            Op::GetFirstKeyValue,
            Op::GetLastKeyValue,
            Op::Delete(150),
            Op::GetFirstKeyValue,
            Op::GetLastKeyValue,
            Op::Delete(100),
            Op::GetFirstKeyValue,
            Op::GetLastKeyValue,
        ]);
    }

    #[test]
    fn test_hardcoded_16_range() {
        run_operations(vec![
            Op::Insert(3, 0),
            Op::Insert(9952, 0),
            Op::Insert(9970, 0),
            Op::Insert(0, 0),
            Op::Insert(9982, 0),
            Op::Insert(4, 0),
            Op::Insert(5, 0),
            Op::Delete(9982),
            Op::Delete(9970),
            Op::GetLastKeyValue,
            Op::IterRange(None, None),
            Op::IterRange(Some(0), None),
            Op::IterRange(None, Some(0)),
            Op::IterRange(Some(0), Some(0)),
        ]);
    }

    proptest! {
        #[test]
        fn test_merkle_btree_txn_against_btreemap(operations in proptest::collection::vec(
            prop_oneof![
                100 => (0..10000u32, any::<u32>()).prop_map(|(k, v)| Op::Insert(k, v)),
                50 => (0..10000u32).prop_map(Op::Get),
                50 => (0..10000u32).prop_map(Op::Delete),
                20 => Just(Op::GetFirstKeyValue),
                20 => Just(Op::GetLastKeyValue),
                10 => Just(Op::IterAll),
                15 => (proptest::option::of(0..10000u32), proptest::option::of(0..10000u32))
                    .prop_map(|(s, e)| Op::IterRange(s, e)),
            ],
            1..10_000
        )) {
            run_operations(operations);
        }
    }
}
