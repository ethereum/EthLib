//! Keys, messages and signatures for the BLS generators.
//!
//! Keys and signatures come from the `bls12_381` crate, independent of the Lean code under test.
//! The values follow the consensus-specs BLS generators, so the pinned cases come out byte for byte.

use std::sync::LazyLock;

use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
use bls12_381::{G1Affine, G2Affine, G2Projective, Scalar};
use ethlib_vectors::Bytes;
use sha2::Sha256;

/// The domain separation tag of the proof-of-possession ciphersuite.
///
/// Ethereum signs with this suite, per consensus-specs `phase0/beacon-chain.md`.
const DST: &[u8] = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";

/// The messages the valid cases sign, numbered as the case names number them.
pub(crate) static MESSAGES: [[u8; 32]; 3] = [[0x00; 32], [0x56; 32], [0xab; 32]];

/// The message of the case with an infinity public key.
pub(crate) const SAMPLE_MESSAGE: [u8; 32] = [0x12; 32];

/// The secret keys, as big-endian integers below the group order.
const SECRET_KEYS: [&str; 3] = [
    "263dbd792f5b1be47ed85f8938c0f29586af0d3ac7b977f21c278fe1462040e3",
    "47b8192d77bf871b62e87859d653922725724a5c031afeabc60bcef5ff665138",
    "328388aff0d4a5b7dc9205abd374e7e98f3cd9f3418edb4eafda5fb16473d216",
];

/// The secret keys as scalars.
pub(crate) static PRIVKEYS: LazyLock<[Scalar; 3]> = LazyLock::new(|| {
    SECRET_KEYS.map(|key| {
        // The crate reads scalars little-endian.
        let mut bytes: [u8; 32] = hex::decode(key).expect("valid hex").try_into().expect("32 bytes");
        bytes.reverse();
        Scalar::from_bytes(&bytes).expect("a secret key is below the group order")
    })
});

/// 48 zero bytes: the compression flag is clear, so this is not a compressed point.
pub(crate) const ZERO_PUBKEY: [u8; 48] = [0; 48];

/// 96 zero bytes: not a compressed point, for the same reason.
pub(crate) const ZERO_SIGNATURE: [u8; 96] = [0; 96];

/// The compressed G1 point at infinity: `0xc0` followed by zeros.
pub(crate) static G1_POINT_AT_INFINITY: LazyLock<[u8; 48]> = LazyLock::new(|| G1Affine::identity().to_compressed());

/// The compressed G2 point at infinity: `0xc0` followed by zeros.
pub(crate) static G2_POINT_AT_INFINITY: LazyLock<[u8; 96]> = LazyLock::new(|| G2Affine::identity().to_compressed());

/// The public key of a secret key: `sk * G1`, compressed.
pub(crate) fn sk_to_pk(sk: &Scalar) -> Bytes {
    G1Affine::from(G1Affine::generator() * sk).to_compressed().into()
}

/// The point a signature on `message` is a multiple of: `hash_to_curve(message)` in G2.
fn hash_to_g2(message: &[u8]) -> G2Projective {
    <G2Projective as HashToCurve<ExpandMsgXmd<Sha256>>>::hash_to_curve([message], DST)
}

/// The aggregate of each key's signature on one message, compressed.
///
/// Every key signs the same message, so the aggregate is `(sum_i sk_i) * H(m)`.
/// It is computed as the sum of the individual signatures, as an aggregator would.
pub(crate) fn aggregate_signature<'a>(keys: impl IntoIterator<Item = &'a Scalar>, message: &[u8]) -> Bytes {
    let h = hash_to_g2(message);
    let sum: G2Projective = keys.into_iter().map(|sk| h * sk).sum();
    G2Affine::from(sum).to_compressed().into()
}
