//! The BLS signature helpers the Ethereum consensus layer adds to the IETF scheme.
//!
//! Both follow `ethereum/consensus-specs`, `altair/bls.md`.
//! They build on the IETF BLS signature draft, ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.

use std::sync::OnceLock;

use crate::Error;
use crate::lean::{self, LeanObject, Object, run_bool, run_bytes};

// The `@[export]` symbols of `EthLib/Cryptography/Bls`.
//
// Each export consumes its arguments and returns an owned IO result.
unsafe extern "C" {
    fn eth_bls_const_bytes_per_pubkey(unit: *mut LeanObject) -> u64;
    fn eth_bls_const_bytes_per_signature(unit: *mut LeanObject) -> u64;

    fn eth_bls_aggregate_pubkeys(pubkeys: *mut LeanObject) -> *mut LeanObject;
    fn eth_bls_fast_aggregate_verify(
        pubkeys: *mut LeanObject,
        message: *mut LeanObject,
        signature: *mut LeanObject,
    ) -> *mut LeanObject;
}

/// The sizes of the BLS objects, read from Lean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct Constants {
    /// Bytes in one compressed G1 public key.
    pub bytes_per_pubkey: usize,
    /// Bytes in one compressed G2 signature.
    pub bytes_per_signature: usize,
}

/// The BLS sizes, read from Lean on first use.
///
/// # Panics
///
/// Panics if the Lean modules failed to initialize.
#[must_use]
pub fn constants() -> &'static Constants {
    static CONSTANTS: OnceLock<Constants> = OnceLock::new();
    CONSTANTS.get_or_init(|| {
        lean::enter();
        Constants {
            bytes_per_pubkey: size(eth_bls_const_bytes_per_pubkey),
            bytes_per_signature: size(eth_bls_const_bytes_per_signature),
        }
    })
}

/// Read one size from its Lean accessor.
fn size(accessor: unsafe extern "C" fn(*mut LeanObject) -> u64) -> usize {
    // SAFETY: every accessor takes the unit value and returns a plain integer.
    let value = unsafe { accessor(lean::unit()) };
    usize::try_from(value).expect("a BLS size fits in memory")
}

/// The sum of the public keys, as one compressed G1 point.
///
/// # Errors
///
/// Rejects an empty list, and any key that fails key validation, such as the point at infinity.
pub fn eth_aggregate_pubkeys<B: AsRef<[u8]>>(pubkeys: &[B]) -> Result<Vec<u8>, Error> {
    let pubkeys = Object::byte_arrays(pubkeys);
    // SAFETY: the export consumes its argument and returns an owned `IO ByteArray`.
    unsafe { run_bytes(eth_bls_aggregate_pubkeys(pubkeys.into_raw())) }
}

/// Whether `signature` signs `message` under the sum of the public keys.
///
/// With no public key, only the G2 point at infinity is accepted.
///
/// # Panics
///
/// Panics if Lean throws.
/// The Lean function returns a plain boolean, so it never does.
#[must_use]
pub fn eth_fast_aggregate_verify<B: AsRef<[u8]>>(pubkeys: &[B], message: &[u8], signature: &[u8]) -> bool {
    let pubkeys = Object::byte_arrays(pubkeys);
    let (message, signature) = (Object::byte_array(message), Object::byte_array(signature));
    // SAFETY: the export consumes its arguments and returns an owned `IO UInt8`.
    let verdict = unsafe {
        run_bool(eth_bls_fast_aggregate_verify(pubkeys.into_raw(), message.into_raw(), signature.into_raw()))
    };
    verdict.expect("the BLS verifier returns a verdict for every input")
}
