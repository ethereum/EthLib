"""BLS12-381 signatures and validator key derivation."""

from ethlib.cryptography._native import (
    BYTES_PER_PUBKEY,
    BYTES_PER_SIGNATURE,
    bls_aggregate as aggregate,
    bls_aggregate_verify as aggregate_verify,
    bls_decode_g1 as decode_g1,
    bls_decode_g2 as decode_g2,
    bls_derive_child_sk as derive_child_sk,
    bls_derive_master_sk as derive_master_sk,
    bls_derive_path as derive_path,
    bls_expand_message_xmd as expand_message_xmd,
    bls_fast_aggregate_verify as fast_aggregate_verify,
    bls_hash_to_g2 as hash_to_g2,
    bls_key_gen as _key_gen,
    bls_pairing as pairing,
    bls_pop_prove as pop_prove,
    bls_pop_verify as pop_verify,
    bls_sign as sign,
    bls_signing_path as signing_path,
    bls_verify as verify,
    bls_withdrawal_path as withdrawal_path,
    eth_aggregate_pubkeys,
    eth_fast_aggregate_verify,
)
from ethlib.errors import BlsError, KeyDerivationError


def key_gen(ikm: bytes, key_info: bytes = b"") -> bytes:
    """
    A secret key, as 32 big-endian bytes, from at least 32 bytes of keying material.

    The keying material and the key are secret, and EthLib makes no constant-time claim.
    """
    return _key_gen(ikm, key_info)


__all__ = [
    "eth_aggregate_pubkeys",
    "eth_fast_aggregate_verify",
    "key_gen",
    "derive_master_sk",
    "derive_child_sk",
    "derive_path",
    "withdrawal_path",
    "signing_path",
    "sign",
    "verify",
    "aggregate",
    "aggregate_verify",
    "fast_aggregate_verify",
    "pop_prove",
    "pop_verify",
    "decode_g1",
    "decode_g2",
    "expand_message_xmd",
    "hash_to_g2",
    "pairing",
    "BYTES_PER_PUBKEY",
    "BYTES_PER_SIGNATURE",
    "BlsError",
    "KeyDerivationError",
]
