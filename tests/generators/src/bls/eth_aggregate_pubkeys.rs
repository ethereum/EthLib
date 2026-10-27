//! `eth_aggregate_pubkeys`: the sum of a list of public keys.

use ethlib::{Error, bls};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{G1_POINT_AT_INFINITY, PRIVKEYS, ZERO_PUBKEY, sk_to_pk};
use crate::{Cases, Operation};

/// The keys to sum, written as a bare list.
#[derive(Serialize)]
pub(crate) struct EthAggregatePubkeys(Vec<Bytes>);

impl Operation for EthAggregatePubkeys {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "eth_aggregate_pubkeys";
    type Output = Bytes;

    fn run(&self) -> Result<Bytes, Error> {
        bls::eth_aggregate_pubkeys(&self.0).map(Bytes)
    }

    /// Sums of valid keys, then lists that key validation rejects.
    fn cases(cases: &mut Cases<'_, Self>) {
        // One key alone: the sum is the key itself.
        for (i, sk) in PRIVKEYS.iter().enumerate() {
            cases.valid(format!("valid_{i}"), || Self(vec![sk_to_pk(sk)]));
        }
        cases.valid("valid_pubkeys", || Self(PRIVKEYS.iter().map(sk_to_pk).collect()));

        // Rejected lists.
        //
        //     empty_list      : no key to sum
        //     zero_pubkey     : compression flag clear, so not a compressed point
        //     infinity_pubkey : the identity, which key validation refuses
        //     x40_pubkey      : only the infinity flag set, without the compression flag
        cases.invalid("empty_list", || Self(Vec::new()));
        cases.invalid("zero_pubkey", || Self(vec![ZERO_PUBKEY.into()]));
        cases.invalid("infinity_pubkey", || Self(vec![Bytes::from(*G1_POINT_AT_INFINITY)]));
        cases.invalid("x40_pubkey", || {
            let mut x40 = [0; 48];
            x40[0] = 0x40;
            Self(vec![x40.into()])
        });
    }
}
