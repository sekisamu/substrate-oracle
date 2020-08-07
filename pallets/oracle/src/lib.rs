/// WARNING! just raw ideas. do not try to compile and run it.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{decl_module, decl_storage, decl_event, decl_error, dispatch, traits::Get};
use frame_system::ensure_signed;
use codec::{Encode, Decode};
use sp_runtime::{
	Percent, Permill, PerU16, PerThing, RuntimeDebug, DispatchError,
	curve::PiecewiseLinear,
	traits::{
		Convert, Zero, StaticLookup, CheckedSub, Saturating, SaturatedConversion,
		AtLeast32BitUnsigned, Dispatchable,
	}};


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

type StorageKey = Vec<u8>;

pub trait Trait: frame_system::Trait {
	/// Because this pallet emits events, it depends on the runtime's definition of an event.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
}

decl_storage! {
	// A unique name is used to ensure that the pallet's storage items are isolated.
	// This name may be updated, but each pallet in the runtime must use a unique name.
	// ---------------------------------vvvvvvvvvvvvvv
	trait Store for Module<T: Trait> as Oracle {
		pub ActiveParamTypes get(fn all_types): Vec<StorageKey>;

		pub ActiveProviders get(fn all_providers): Vec<T::AccountId>;

		pub DataFeeds get(fn member_score): double_map hasher(blake2_128_concat) StorageKey,
			hasher(blake2_128_concat) T::AccountId => [PrimitiveOracleType; u32];
	}
}


decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {

		// Events must be initialized if they are used by the pallet.
		fn deposit_event() = default;



	}
}