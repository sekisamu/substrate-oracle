#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
    decl_error, decl_event, decl_module, decl_storage, dispatch, traits::Get,
    IterableStorageDoubleMap, IterableStorageMap,
};
use frame_system::{ensure_root, ensure_signed};

use codec::{Decode, Encode};
use sp_runtime::{
    curve::PiecewiseLinear,
    traits::{
        AtLeast32BitUnsigned, CheckedSub, Convert, Dispatchable, SaturatedConversion, Saturating,
        StaticLookup, Zero,
    },
    DispatchError, DispatchResult, PerThing, PerU16, Percent, Permill, RuntimeDebug,
};
use sp_std::prelude::*;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum Operations {
    Average,
    Sum,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Encode, Decode, RuntimeDebug)]
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

impl PrimitiveOracleType {
    pub fn number_type(&self) -> NumberType {
        match self {
            PrimitiveOracleType::U8(_) => NumberType::U8,
            PrimitiveOracleType::U16(_) => NumberType::U16,
            PrimitiveOracleType::U32(_) => NumberType::U32,
            PrimitiveOracleType::U64(_) => NumberType::U64,
            PrimitiveOracleType::U128(_) => NumberType::U128,
            PrimitiveOracleType::I8(_) => NumberType::I8,
            PrimitiveOracleType::I16(_) => NumberType::I16,
            PrimitiveOracleType::I32(_) => NumberType::I32,
            PrimitiveOracleType::I64(_) => NumberType::I64,
            PrimitiveOracleType::I128(_) => NumberType::I128,
            PrimitiveOracleType::Percent(_) => NumberType::Percent,
            PrimitiveOracleType::Permill(_) => NumberType::Permill,
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum NumberType {
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Percent,
    Permill,
}
/*
impl NumberType {
    pub fn init_primitive_type(&self) -> PrimitiveOracleType {
        match self {
            NumberType::U8 => PrimitiveOracleType::U8(Default::default()),
            NumberType::U16 => PrimitiveOracleType::U16(Default::default()),
            NumberType::U32 => PrimitiveOracleType::U32(Default::default()),
            NumberType::U64 => PrimitiveOracleType::U64(Default::default()),
            NumberType::U128 => PrimitiveOracleType::U128(Default::default()),
            NumberType::I8 => PrimitiveOracleType::I8(Default::default()),
            NumberType::I16 => PrimitiveOracleType::I16(Default::default()),
            NumberType::I32 => PrimitiveOracleType::I32(Default::default()),
            NumberType::I64 => PrimitiveOracleType::I64(Default::default()),
            NumberType::I128 => PrimitiveOracleType::I128(Default::default()),
            NumberType::Percent => PrimitiveOracleType::Percent(Default::default()),
            NumberType::Permill => PrimitiveOracleType::Permill(Default::default()),
        }
    }
}*/

impl Default for PrimitiveOracleType {
    fn default() -> Self {
        PrimitiveOracleType::U8(0)
    }
}

type StorageKey = Vec<u8>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub struct Info<BlockNumber> {
    number_type: NumberType,
    operation: Operations,
    schedule: BlockNumber,
}

const RING_BUF_LEN: usize = 8;

use frame_support::traits::{EnsureOrigin, Contains};
use sp_std::{marker::PhantomData, prelude::*};

pub struct DataFeedGet<Key: Get<[u8; 32]>, Value: Get<PrimitiveOracleType>>(
    PhantomData<Key>,
    PhantomData<Value>,
);
impl<Key: Get<[u8; 32]>, Value: Get<PrimitiveOracleType>> Get<PrimitiveOracleType>
    for DataFeedGet<Key, Value>
{
    fn get() -> PrimitiveOracleType {
        frame_support::storage::unhashed::get_or(Key::get().as_ref(), Value::get())
    }
}

pub trait Trait: frame_system::Trait {
    /// Because this pallet emits events, it depends on the runtime's definition of an event.
    type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

    /// The origin that can schedule an update
    type DispatchOrigin: EnsureOrigin<Self::Origin, Success=Self::AccountId>;
}

decl_event!(
    pub enum Event<T>
    where
        AccountId = <T as frame_system::Trait>::AccountId,
    {
        SomethingStored(u32, AccountId),
    }
);

// Errors inform users that something went wrong.
decl_error! {
    pub enum Error for Module<T: Trait> {
        ExistedKey,
        InvalidKey,
        InvalidValue,
    }
}

decl_storage! {
    // A unique name is used to ensure that the pallet's storage items are isolated.
    // This name may be updated, but each pallet in the runtime must use a unique name.
    // ---------------------------------vvvvvvvvvvvvvv
    trait Store for Module<T: Trait> as Oracle {
        pub ActiveParamTypes get(fn all_types): Vec<StorageKey>;

        pub ActiveProviders get(fn all_providers): Vec<T::AccountId>;

        // pub LastUpdated get(fn last_updated): hasher(twox_64_concat) StorageKey => T::BlockNumebr;

        pub Infos get(fn infos): map hasher(twox_64_concat) StorageKey => Option<Info<T::BlockNumber>>;

        pub DataFeeds get(fn member_score): double_map hasher(blake2_128_concat) StorageKey,
            hasher(blake2_128_concat) T::AccountId => Option<[PrimitiveOracleType; RING_BUF_LEN]>;
    }
}

impl<T: Trait> Contains<T::AccountId> for Module <T> {
    fn sorted_members() -> Vec<T::AccountId> {
        Self::all_providers()
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        // Events must be initialized if they are used by the pallet.
        fn deposit_event() = default;

        #[weight = 0]
        pub fn register_storage_key(origin, key: StorageKey, info: Info<T::BlockNumber>) -> DispatchResult {
            T::DispatchOrigin::try_origin(origin).map(|_| ()).or_else(ensure_root)?;
            // parse origin
            ActiveParamTypes::try_mutate::<_, DispatchError, _>(|v| {
                if v.contains(&key) {
                    return Err(Error::<T>::ExistedKey)?;
                }
                v.push(key.clone());
                Ok(())
            })?;
            Infos::<T>::insert(key, info);
            Ok(())
        }

        #[weight = 0]
        pub fn remove_storage_key(origin, key: StorageKey) -> DispatchResult {
            T::DispatchOrigin::try_origin(origin).map(|_| ()).or_else(ensure_root)?;
            ActiveParamTypes::mutate(|v| {
                // remove key
                v.retain(|k| k != &key);
            });
            Infos::<T>::remove(&key);
            DataFeeds::<T>::remove_prefix(&key);
            Ok(())
        }

        #[weight = 0]
        pub fn feed_data(origin, key: StorageKey, value: PrimitiveOracleType) -> DispatchResult {
            let who = T::DispatchOrigin::ensure_origin(origin)?;
            Self::feed_data_impl(who, key, value)
        }

        fn on_finalize(_n: T::BlockNumber) {
            for (key, info) in Infos::<T>::iter() {
                if info.schedule % _n == Zero::zero() {
                    Self::calc(key, info);
                }
            }
        }
    }
}
impl<T: Trait> Module<T> {
    fn feed_data_impl(who: T::AccountId, key: StorageKey, value: PrimitiveOracleType) -> DispatchResult {
        if !Self::all_types().contains(&key) {
            Err(Error::<T>::InvalidKey)?
        }
        let info: Info<_> = Self::infos(&key).ok_or(Error::<T>::InvalidKey)?;
        if value.number_type() != info.number_type {
            Err(Error::<T>::InvalidValue)?
        }
        DataFeeds::<T>::try_mutate_exists(key, who, |data| {
            match data {
                Some(data) => {
                    let mut new_data = [Default::default(); RING_BUF_LEN];
                    new_data[0] = value;
                    // move data buf to new_data buf, and drop last item
                    new_data[1..].copy_from_slice(&data[0.. (data.len() - 2)]);
                    *data = new_data;
                },
                None => {
                    *data = Some([value; RING_BUF_LEN]);
                }
            }
            Ok(())
        })
    }

    fn calc(key: StorageKey, info: Info<T::BlockNumber>) {
        for (account_id, datas) in DataFeeds::<T>::drain_prefix(&key) {
            match info.operation {
                Operations::Sum => {
                    // TODO
                    PrimitiveOracleType::default()
                }
                Operations::Average => {
                    // TODO
                    PrimitiveOracleType::default()
                }
            };
        }
        // TODO
        let value = PrimitiveOracleType::default();
        Self::set_storage_value(key, value);
    }

    fn set_storage_value(key: Vec<u8>, value: PrimitiveOracleType) {
        frame_support::storage::unhashed::put(&key, &value);
    }
}

// fn calc(src: &[PrimitiveOracleType], expect_type: NumberType, op: Operations) -> PrimitiveOracleType {
//     src.iter().filter(|item| *item.number_type() == expect_type)
// }