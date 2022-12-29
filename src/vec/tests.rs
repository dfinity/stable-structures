use super::{InitError, Vec as StableVec};
use crate::storable::{BoundedStorable, Storable};
use crate::vec_mem::VectorMemory as M;
use proptest::collection::vec as pvec;
use proptest::prelude::*;
use std::fmt::Debug;

#[derive(Debug, Clone, PartialEq)]
struct UnfixedU64<const N: u32>(u64);

impl<const N: u32> Storable for UnfixedU64<N> {
    fn to_bytes(&self) -> std::borrow::Cow<'_, [u8]> {
        self.0.to_bytes()
    }

    fn from_bytes(bytes: Vec<u8>) -> Self {
        assert!(bytes.len() == 8);
        Self(u64::from_bytes(bytes))
    }
}

impl<const N: u32> BoundedStorable for UnfixedU64<N> {
    const MAX_SIZE: u32 = N;
    const IS_FIXED_SIZE: bool = false;
}

#[derive(Debug, PartialEq, Clone)]
enum Operation<T> {
    Push(T),
    Pop,
}

fn arb_unfixed<const N: u32>(
    s: impl Strategy<Value = u64>,
) -> impl Strategy<Value = UnfixedU64<N>> {
    s.prop_map(UnfixedU64)
}

fn arb_op<T: Clone + Debug>(s: impl Strategy<Value = T>) -> impl Strategy<Value = Operation<T>> {
    prop_oneof![
        3 => s.prop_map(Operation::Push),
        1 => Just(Operation::Pop),
    ]
}

proptest! {
    #[test]
    fn push_pop_model_u64(ops in pvec(arb_op(any::<u64>()), 40)) {
        check_push_pop_model(ops)?;
    }

    #[test]
    fn push_pop_model_unfixed_255(ops in pvec(arb_op(arb_unfixed::<255>(any::<u64>())), 40)) {
        check_push_pop_model(ops)?;
    }

   #[test]
   fn push_pop_model_unfixed_65000(ops in pvec(arb_op(arb_unfixed::<65000>(any::<u64>())), 10)) {
       check_push_pop_model(ops)?;
   }

   #[test]
   fn push_pop_model_unfixed_68000(ops in pvec(arb_op(arb_unfixed::<68000>(any::<u64>())), 10)) {
       check_push_pop_model(ops)?;
   }

    #[test]
    fn init_after_new(vals in pvec(any::<u64>(), 0..20)) {
        let sv = StableVec::<u64, M>::new(M::default()).unwrap();
        for v in vals {
            sv.push(&v).unwrap();
        }
        let vec = sv.to_vec();
        prop_assert_eq!(StableVec::<u64, M>::init(sv.forget()).unwrap().to_vec(), vec);
    }
}

fn check_push_pop_model<T: BoundedStorable + Debug + Clone + PartialEq>(
    ops: Vec<Operation<T>>,
) -> Result<(), TestCaseError> {
    let mut v = Vec::new();
    let sv = StableVec::<T, M>::new(M::default()).unwrap();

    for op in ops {
        match op {
            Operation::Push(x) => {
                sv.push(&x).unwrap();
                v.push(x);
                prop_assert_eq!(&sv.to_vec(), &v);
            }
            Operation::Pop => {
                prop_assert_eq!(sv.pop(), v.pop());
                prop_assert_eq!(&sv.to_vec(), &v);
            }
        }
    }
    Ok(())
}

#[test]
fn test_init_type_compatibility() {
    let v = StableVec::<u64, M>::new(M::default()).unwrap();

    assert_eq!(
        StableVec::<u32, M>::init(v.forget()).unwrap_err(),
        InitError::IncompatibleElementType
    );

    let v = StableVec::<u64, M>::new(M::default()).unwrap();
    assert_eq!(
        StableVec::<UnfixedU64<8>, M>::init(v.forget()).unwrap_err(),
        InitError::IncompatibleElementType
    );
}
