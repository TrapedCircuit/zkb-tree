use alloc::rc::Rc;
use alloc::sync::Arc;

use crate::hash::{PortableHash, PortableHasher};
use crate::{
    errors::BTreeError,
    node::{InnerOuterSnapshotRef, NodeHash},
};

pub type Idx = u32;

pub trait Store {
    type Key: Ord + Clone + PortableHash;
    type Value: Clone + PortableHash;

    fn get_store_root_idx(&self) -> Option<Idx>;
    fn get_store_root_hash(&self) -> NodeHash;

    fn calc_subtree_hash(
        &self,
        hasher: &mut impl PortableHasher<32>,
        hash_idx: Idx,
    ) -> Result<NodeHash, BTreeError>;

    fn get(
        &self,
        hash_idx: Idx,
    ) -> Result<InnerOuterSnapshotRef<'_, Self::Key, Self::Value>, BTreeError>;
}

macro_rules! impl_store_deref {
    ($wrapper:ty) => {
        impl<S: Store> Store for $wrapper {
            type Key = S::Key;
            type Value = S::Value;

            #[inline(always)]
            fn get_store_root_idx(&self) -> Option<Idx> {
                (**self).get_store_root_idx()
            }
            #[inline(always)]
            fn get_store_root_hash(&self) -> NodeHash {
                (**self).get_store_root_hash()
            }
            #[inline(always)]
            fn calc_subtree_hash(
                &self,
                hasher: &mut impl PortableHasher<32>,
                hash_idx: Idx,
            ) -> Result<NodeHash, BTreeError> {
                (**self).calc_subtree_hash(hasher, hash_idx)
            }
            #[inline(always)]
            fn get(
                &self,
                hash_idx: Idx,
            ) -> Result<InnerOuterSnapshotRef<'_, Self::Key, Self::Value>, BTreeError> {
                (**self).get(hash_idx)
            }
        }
    };
}

impl_store_deref!(&S);
impl_store_deref!(Rc<S>);
impl_store_deref!(Arc<S>);
