from .._native import (
    eth_aggregate_pubkeys,
    eth_fast_aggregate_verify,
    bls_key_gen as _key_gen,
    bls_sign as sign,
    bls_verify as verify,
    bls_aggregate as aggregate,
    bls_aggregate_verify as aggregate_verify,
    bls_fast_aggregate_verify as fast_aggregate_verify,
    bls_pop_prove as pop_prove,
    bls_pop_verify as pop_verify,
    bls_expand_message_xmd as expand_message_xmd,
    bls_hash_to_g2 as hash_to_g2,
    BYTES_PER_PUBKEY,
    BYTES_PER_SIGNATURE,
)


def key_gen(ikm: bytes, key_info: bytes = b"") -> bytes:
    """A secret key, as 32 big-endian bytes, from at least 32 bytes of keying material.

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
    "expand_message_xmd",
    "hash_to_g2",
    "BYTES_PER_PUBKEY",
    "BYTES_PER_SIGNATURE",
]
