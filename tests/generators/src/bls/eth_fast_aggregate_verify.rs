//! `eth_fast_aggregate_verify`: check one signature by many keys on one message.

use ethlib::{Error, bls};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{
    G1_POINT_AT_INFINITY, G2_POINT_AT_INFINITY, MESSAGES, PRIVKEYS, SAMPLE_MESSAGE, ZERO_SIGNATURE,
    aggregate_signature, sk_to_pk,
};
use crate::{Cases, Operation};

/// Keys, the message they signed, and their aggregate signature.
#[derive(Serialize)]
pub(crate) struct EthFastAggregateVerify {
    pubkeys: Vec<Bytes>,
    message: Bytes,
    signature: Bytes,
}

impl EthFastAggregateVerify {
    /// The first `i + 1` keys, and their aggregate signature on message `i`.
    fn signed(i: usize) -> Self {
        let keys = &PRIVKEYS[..=i];
        Self {
            pubkeys: keys.iter().map(sk_to_pk).collect(),
            message: MESSAGES[i].into(),
            signature: aggregate_signature(keys, &MESSAGES[i]),
        }
    }
}

impl Operation for EthFastAggregateVerify {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "eth_fast_aggregate_verify";
    type Output = bool;

    fn run(&self) -> Result<bool, Error> {
        // The specification returns false on malformed input, so nothing is rejected.
        Ok(bls::eth_fast_aggregate_verify(&self.pubkeys, &self.message, &self.signature))
    }

    /// Honest aggregates, three ways to break one, and the two empty-key cases.
    fn cases(cases: &mut Cases<'_, Self>) {
        for i in 0..MESSAGES.len() {
            // Case i signs message i with the first i + 1 keys.
            cases.returns(format!("valid_{i}"), true, move || Self::signed(i));

            // Mutation: one more key than signed.
            //
            //     keys  : pk_0 .. pk_i, pk_2
            //     signed: sk_0 .. sk_i
            cases.returns(format!("extra_pubkey_{i}"), false, move || {
                let mut input = Self::signed(i);
                input.pubkeys.push(sk_to_pk(&PRIVKEYS[PRIVKEYS.len() - 1]));
                input
            });

            // Mutation: the last four signature bytes set to 0xff.
            cases.returns(format!("tampered_signature_{i}"), false, move || {
                let mut input = Self::signed(i);
                let tail = input.signature.len() - 4;
                input.signature[tail..].fill(0xff);
                input
            });
        }

        // With no key, the specification accepts the G2 point at infinity, and nothing else.
        let no_keys = |signature: &[u8]| Self {
            pubkeys: Vec::new(),
            message: MESSAGES[MESSAGES.len() - 1].into(),
            signature: signature.into(),
        };
        cases.returns("na_pubkeys_and_infinity_signature", true, move || no_keys(&*G2_POINT_AT_INFINITY));
        cases.returns("na_pubkeys_and_zero_signature", false, move || no_keys(&ZERO_SIGNATURE));

        // Mutation: the identity appended to three honest keys.
        //
        // The sum is unchanged, but key validation rejects the identity, so the check fails.
        cases.returns("infinity_pubkey", false, || Self {
            pubkeys: PRIVKEYS.iter().map(sk_to_pk).chain([Bytes::from(*G1_POINT_AT_INFINITY)]).collect(),
            message: SAMPLE_MESSAGE.into(),
            signature: aggregate_signature(PRIVKEYS.iter(), &SAMPLE_MESSAGE),
        });
    }
}
