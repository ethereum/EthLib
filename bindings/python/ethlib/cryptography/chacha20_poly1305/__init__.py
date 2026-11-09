"""ChaCha20, Poly1305 and the ChaCha20-Poly1305 AEAD of RFC 8439."""

from ethlib.cryptography._native import (
    CHACHA20_BLOCK_SIZE,
    CHACHAPOLY_KEY_SIZE,
    CHACHAPOLY_NONCE_SIZE,
    CHACHAPOLY_TAG_SIZE,
    chacha20_block,
    chacha20_crypt,
    chacha20_poly1305_decrypt,
    chacha20_poly1305_encrypt,
    chacha20_quarter_round,
    chacha20_quarter_round_state,
    poly1305,
    poly1305_key,
)
from ethlib.errors import ChaCha20Poly1305Error

# The keys are secret.
# EthLib makes no constant-time claim, and the tag comparison is not constant-time.
# RFC 8439 §4 requires a constant-time tag comparison in online protocols.

__all__ = [
    "CHACHA20_BLOCK_SIZE",
    "CHACHAPOLY_KEY_SIZE",
    "CHACHAPOLY_NONCE_SIZE",
    "CHACHAPOLY_TAG_SIZE",
    "ChaCha20Poly1305Error",
    "chacha20_block",
    "chacha20_crypt",
    "chacha20_poly1305_decrypt",
    "chacha20_poly1305_encrypt",
    "chacha20_quarter_round",
    "chacha20_quarter_round_state",
    "poly1305",
    "poly1305_key",
]
