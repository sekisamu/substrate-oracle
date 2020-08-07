#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{decl_error, decl_event, decl_module, decl_storage, dispatch, traits::Get};
use frame_system::ensure_signed;

use codec::{Decode, Encode};
use sp_runtime::{
    curve::PiecewiseLinear,
    traits::{
        AtLeast32BitUnsigned, CheckedSub, Convert, Dispatchable, SaturatedConversion, Saturating,
        StaticLookup, Zero,
    },
    DispatchError, PerThing, PerU16, Percent, Permill, RuntimeDebug,
};
use sp_std::prelude::*;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, RuntimeDebug)]
pub enum PrimitiveOracleType {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    Percent(Percent),
    Permill(Permill),
}

impl Default for PrimitiveOracleType {
    fn default() -> Self {
        PrimitiveOracleType::U8(0)
    }
}

type StorageKey = Vec<u8>;

const RING_BUF_LEN: usize = 8;

use sp_std::{marker::PhantomData, prelude::*};
pub struct DataFeedGet<Key: Get<[u8; 32]>, Type:Decode + Sized, Value: Get<Type> >(
	PhantomData<Key>,
	PhantomData<Type>,
	PhantomData<Value>,
);
impl<Type:Decode + Sized, Key: Get<[u8; 32]>, Value: Get<Type>> Get<Type> for DataFeedGet<Key, Type, Value> {
	fn get() -> Type {
		frame_support::storage::unhashed::get_or(Key::get().as_ref(), Value::get())
	}
}

pub trait Trait: frame_system::Trait {
    /// Because this pallet emits events, it depends on the runtime's definition of an event.
    type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
}

decl_event!(
    pub enum Event<T>
    where
        AccountId = <T as frame_system::Trait>::AccountId,
    {
        SomethingStored(u32, AccountId),
    }
);

decl_storage! {
    // A unique name is used to ensure that the pallet's storage items are isolated.
    // This name may be updated, but each pallet in the runtime must use a unique name.
    // ---------------------------------vvvvvvvvvvvvvv
    trait Store for Module<T: Trait> as Oracle {
        pub ActiveParamTypes get(fn all_types): Vec<StorageKey>;

        pub ActiveProviders get(fn all_providers): Vec<T::AccountId>;

        pub DataFeeds get(fn member_score): double_map hasher(blake2_128_concat) StorageKey,
            hasher(blake2_128_concat) T::AccountId => [PrimitiveOracleType; RING_BUF_LEN];
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        // Events must be initialized if they are used by the pallet.
        fn deposit_event() = default;

        #[weight = 0]
		pub fn register_storage_key(origin, key: Vec<u8>) {
			// parse origin
			// e.g. the key is b":Fxck:"
			StorageKeys::mutate(|v| {
				if !v.contains(&key) {
					v.push(key)
				}
			});
		}
    }
}
impl<T: Trait> Module<T> {
	fn set_storage_value(key: Vec<u8>, value: Vec<u8>) {
		// e.g. receive to set key b":Fxck:" in period end, value is u64.encode()
		frame_support::storage::unhashed::put(&key, &value);
	}
}