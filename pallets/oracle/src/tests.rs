
use crate as oracle;
use crate::*;
use codec::{Encode, Decode};
use frame_system::offchain::SigningTypes;
use frame_support::{
	assert_ok, impl_outer_origin, impl_outer_event, parameter_types,
	weights::Weight, traits::OnFinalize,
};
use sp_core::{
	H256,
	offchain::{OffchainExt, TransactionPoolExt, testing},
	sr25519::Signature,
	testing::KeyStore,
	traits::KeystoreExt,
};
use sp_runtime::{
	Perbill, FixedU128, RuntimeAppPublic,
	testing::{Header, TestXt},
	traits::{
		BlakeTwo256, IdentityLookup, Extrinsic as ExtrinsicT,
		IdentifyAccount, Verify,
	},
};

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

impl_outer_event! {
	pub enum TestEvent for Test {
		frame_system<T>,
		pallet_template<T>,
		oracle<T>,
	}
}


#[derive(Clone, Eq, PartialEq, Encode, Decode)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl pallet_template::Trait for Test {
	type Event = TestEvent;
}

type Extrinsic = TestXt<Call<Test>, ()>;
type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

impl frame_system::offchain::SigningTypes for Test {
	type Public = <Signature as Verify>::Signer;
	type Signature = Signature;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test where
	Call<Test>: From<LocalCall>,
{
	type OverarchingCall = Call<Test>;
	type Extrinsic = Extrinsic;
}

impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Test where
	Call<Test>: From<LocalCall>,
{
	fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: Call<Test>,
		_public: <Signature as Verify>::Signer,
		_account: AccountId,
		nonce: u64,
	) -> Option<(Call<Test>, <Extrinsic as ExtrinsicT>::SignaturePayload)> {
		Some((call, (nonce, ())))
	}
}
parameter_types! {
	pub const OperatorAccount: u128 = 1;
}

impl Trait for Test {
	type Event = TestEvent;
	type AuthorityId = crypto::TestAuthId;
	type Call = Call<Test>;
	type DispatchOrigin = frame_system::EnsureSigned<AccountId>;
}

pub type System = frame_system::Module<Test>;
pub type Template = pallet_template::Module<Test>;
pub type Oracle = Module<Test>;

#[test]
fn should_submit_signed_data_on_chain() {
	const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";

	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();
	let keystore = KeyStore::new();
	keystore.write().sr25519_generate_new(
		oracle::crypto::Public::ID,
		Some(&format!("{}/hunter1", PHRASE))
	).unwrap();


	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore.clone()));

	let public_key = keystore.read()
		.sr25519_public_keys(oracle::crypto::Public::ID)
		.get(0)
		.unwrap()
		.clone();

	{
		let mut state = offchain_state.write();

		state.expect_request(testing::PendingRequest {
			method: "GET".into(),
			uri: "https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".into(),
			response: Some(br#"{"USD": 1.56}"#.to_vec()),
			sent: true,
			..Default::default()
		});
	}

	t.execute_with(|| {
		register_info();

		Oracle::add_provider(
			Origin::signed(AccountId::default()),
			public_key
		);

		assert!(Oracle::all_providers().contains(&public_key));

		Oracle::fetch_and_send_signed(
			&<pallet_template::Something2>::hashed_key().to_vec()
		).unwrap();

		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature.unwrap().0, 0);
		assert_eq!(tx.call, Call::feed_data(
			<pallet_template::Something2>::hashed_key().to_vec(),
			super::PrimitiveOracleType::FixedU128(FixedU128::from((156, 100)))
		));

		System::set_block_number(2);
		Oracle::on_finalize(System::block_number());

		assert_eq!(Template::something2().unwrap().into_fixed_u128(), Some(FixedU128::from((156, 100))));
	});




}

pub fn register_info() {
	let data_info = super::Info {
		key_str: "USD".as_bytes().to_vec(),
		number_type: NumberType::FixedU128,
		operation: Operations::Average,
		schedule: 2
	};

	assert_ok!(
		Oracle::register_storage_key(
			Origin::signed(AccountId::default()),
			<pallet_template::Something2>::hashed_key().to_vec(),
			data_info
		)
	);

	assert_ok!(
		Oracle::set_url(
			Origin::signed(AccountId::default()),
			<pallet_template::Something2>::hashed_key().to_vec(),
			"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".as_bytes().to_vec()
		)
	);
}


