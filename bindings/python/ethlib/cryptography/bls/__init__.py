"""BLS signatures on the BLS12-381 curve, with their aggregation and their proofs of possession."""

from ethlib.cryptography._native import (
    BYTES_PER_PUBKEY,
    BYTES_PER_SIGNATURE,
    bls_aggregate as aggregate,
    bls_aggregate_verify as aggregate_verify,
    bls_decode_g1 as decode_g1,
    bls_decode_g2 as decode_g2,
    bls_expand_message_xmd as expand_message_xmd,
    bls_fast_aggregate_verify as fast_aggregate_verify,
    bls_hash_to_g2 as hash_to_g2,
    bls_key_gen as _key_gen,
    bls_pairing as pairing,
    bls_pop_prove as pop_prove,
    bls_pop_verify as pop_verify,
    bls_sign as sign,
    bls_verify as verify,
    eth_aggregate_pubkeys,
    eth_fast_aggregate_verify,
)
from ethlib.errors import BlsError


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
]
