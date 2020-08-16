#![cfg_attr(not(feature = "std"), no_std)]

// TODO: we need to figure out the key function here
// which is how to convert JsonValue::number to PrimitiveOracleType

use frame_support::{
	debug,
	decl_error, decl_event, decl_module, decl_storage, dispatch, traits::Get,
	IterableStorageDoubleMap, IterableStorageMap,
};
use frame_system::{ensure_root, ensure_signed, offchain::{
	AppCrypto, CreateSignedTransaction, SendUnsignedTransaction, SendSignedTransaction,
	SignedPayload, SigningTypes, Signer, SubmitTransaction,
	},
};
use sp_runtime::{
	offchain::{http, Duration, storage::StorageValueRef},
	transaction_validity::{
		InvalidTransaction, ValidTransaction, TransactionValidity, TransactionSource,
		TransactionPriority,
	},
};

use codec::{Decode, Encode};
use sp_runtime::{
	curve::PiecewiseLinear,
	traits::{
		AtLeast32BitUnsigned, CheckedSub, Convert, Dispatchable, SaturatedConversion, Saturating,
		StaticLookup, Zero,
	},
	DispatchError, DispatchResult, PerThing, PerU16, Percent, Permill, RuntimeDebug,
};
use sp_std::{prelude::*, str::Chars};
use lite_json::json::JsonValue;

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
	Percent(Percent),
	Permill(Permill),
}

impl PrimitiveOracleType {
	pub fn number_type(&self) -> NumberType {
		match self {
			PrimitiveOracleType::U8(_) => NumberType::U8,
			PrimitiveOracleType::U16(_) => NumberType::U16,
			PrimitiveOracleType::U32(_) => NumberType::U32,
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
	Percent,
	Permill,
}


impl Default for PrimitiveOracleType {
	fn default() -> Self {
		PrimitiveOracleType::U8(0)
	}
}

type StorageKey = Vec<u8>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, RuntimeDebug)]
pub struct Info<BlockNumber> {
	/// the key of what we want from the json callback
	pub key_str: Vec<u8>,
	number_type: NumberType,
	operation: Operations,
	schedule: BlockNumber,
}

const RING_BUF_LEN: usize = 8;

use frame_support::traits::{Contains, EnsureOrigin};
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

        /// permissioned URL that could be used to fetch data
        pub Url get(fn url): map hasher(twox_64_concat) StorageKey => Vec<u8>;

        pub DataFeeds get(fn member_score): double_map hasher(blake2_128_concat) StorageKey,
            hasher(blake2_128_concat) T::AccountId => Option<[PrimitiveOracleType; RING_BUF_LEN]>;


    }
}

impl<T: Trait> Contains<T::AccountId> for Module<T> {
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

        #[weight = 0]
        pub fn add_provider(origin, new_one: <T::Lookup as StaticLookup>::Source) -> DispatchResult {
            T::DispatchOrigin::try_origin(origin).map(|_| ()).or_else(ensure_root)?;
            let new_one = T::Lookup::lookup(new_one)?;

            ActiveProviders::<T>::mutate(|v| {
                if !v.contains(&new_one) {
                    v.push(new_one);
                }
            });
            Ok(())
        }

        #[weight = 0]
        pub fn remove_provider(origin, who: <T::Lookup as StaticLookup>::Source) -> DispatchResult {
            T::DispatchOrigin::try_origin(origin).map(|_| ()).or_else(ensure_root)?;
            let who = T::Lookup::lookup(who)?;

            ActiveProviders::<T>::mutate(|v| {
                v.retain(|accountid| accountid != &who);
            });
            Ok(())
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
	fn feed_data_impl(
		who: T::AccountId,
		key: StorageKey,
		value: PrimitiveOracleType,
	) -> DispatchResult {
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
					new_data[1..].copy_from_slice(&data[0..(data.len() - 2)]);
					*data = new_data;
				}
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

	fn fetch_data(storage_key: &StorageKey) -> Result<PrimitiveOracleType, http::Error> {
		// We want to keep the offchain worker execution time reasonable, so we set a hard-coded
		// deadline to 2s to complete the external call.
		// You can also wait idefinitely for the response, however you may still get a timeout
		// coming from the host machine.
		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(2_000));
		// TODO: if error
		let url = Self::url(storage_key);

		let request = http::Request::get(
			// TODO: if error
			core::str::from_utf8(&url).unwrap());

		// to alter request headers or stream body content in case of non-GET requests.
		let pending = request
			.deadline(deadline)
			.send()
			.map_err(|_| http::Error::IoError)?;


		let response = pending.try_wait(deadline)
			.map_err(|_| http::Error::DeadlineReached)??;
		// Let's check the status code before we proceed to reading the response.
		if response.code != 200 {
		debug::warn!("Unexpected status code: {}", response.code);
		return Err(http::Error::Unknown);
		}


		let body = response.body().collect::<Vec<u8>>();
		// TODO: handle error here
		let info = Self::infos(&storage_key).unwrap();

		// Create a str slice from the body.
		let body_str = sp_std::str::from_utf8(&body).map_err(|_| {
			debug::warn!("No UTF8 body");
			http::Error::Unknown
		})?;
		// TODO: handle error
		let key_str = core::str::from_utf8(&info.key_str).unwrap().chars();
		let data = match Self::parse_data(key_str, body_str) {
			Some(data) => Ok(data),
			None => {
				debug::warn!("Unable to extract price from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			}
		}?;

//		debug::warn!("Got Data: {}", data);

		Ok(data)
	}

	fn parse_data(key_str: Chars, data: &str) -> Option<PrimitiveOracleType> {
		let mut key_str = key_str;
		let val = lite_json::parse_json(data);
		let output = val.ok().and_then(|v| match v {
			JsonValue::Object(obj) => {
				obj.into_iter().find(
					|(k, _)| k.iter().all(|k| Some(*k) == key_str.next()))
						.and_then(|v| match v.1 {
							JsonValue::Number(number) => Some(number),
							_ => None,
						})
			},
			_ => None,
		})?;

		// TODO: transform number into PrimitiveOracleType
		Some(PrimitiveOracleType::default())
	}


}


