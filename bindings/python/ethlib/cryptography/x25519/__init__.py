"""X25519 of RFC 7748."""

from ethlib.cryptography._native import X25519_KEY_SIZE, x25519, x25519_public_key
from ethlib.errors import X25519Error

# The scalar is secret.
# EthLib makes no constant-time claim.

__all__ = ["X25519_KEY_SIZE", "X25519Error", "x25519", "x25519_public_key"]
