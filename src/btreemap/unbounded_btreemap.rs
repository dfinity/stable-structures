use crate::{Memory, Storable};
use std::marker::PhantomData;

#[allow(dead_code)]
pub struct UnboundedBTreeMap<K, V, M>
where
    K: Storable + Ord + Clone,
    V: Storable,
    M: Memory,
{
    // TODO
    _phantom: PhantomData<(K, V, M)>,
}
