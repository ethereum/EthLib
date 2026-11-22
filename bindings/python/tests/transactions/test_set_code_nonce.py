"""The nonce of a set-code transaction, a 64-bit number."""

# The execution test suites hold no set-code transaction with a nonce of 2^64 or more.
# So each case here is built and signed in the test.

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import sign
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

KEY = bytes(31) + b"\x01"
OTHER = b"\x11" * 20
# One authorization; the check of a transaction does not recover its signer.
AUTHORIZATION = [b"", OTHER, b"", b"", b"\x01", b"\x01"]


def _int(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _signed(kind: int, fields: list) -> bytes:
    """The typed transaction of type `kind` with these fields, signed by the key."""
    signature = sign(KEY, keccak256(bytes([kind]) + rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return bytes([kind]) + rlp.encode(fields + [_int(v), r.lstrip(b"\0"), s.lstrip(b"\0")])


def _set_code(nonce: int) -> bytes:
    """A signed type 4 transaction on chain 1 with the nonce `nonce`."""
    fields = [_int(1), _int(nonce), _int(1), _int(10), _int(100_000), OTHER, b"", b"", []]
    return _signed(4, fields + [[AUTHORIZATION]])


def _fee_market(nonce: int) -> bytes:
    """A signed type 2 transfer on chain 1 with the nonce `nonce`."""
    fields = [_int(1), _int(nonce), _int(1), _int(10), _int(21000), OTHER, _int(1), b"", []]
    return _signed(2, fields)


def test_set_code_nonce_above_64_bits() -> None:
    """A nonce of 2^64 does not fit 64 bits, so the set-code transaction fails to decode."""
    message = "decoding: field 1: scalarTooLarge 18446744073709551616 64"
    with raises(transactions.TransactionError, message):
        transactions.check("pectra", 1, _set_code(2**64))


def test_largest_set_code_nonce() -> None:
    """A nonce of 2^64 - 1 decodes, and the rule of EIP-2681 then refuses it."""
    message = "nonceOverflow (nonce := 18446744073709551615)"
    with raises(transactions.TransactionError, message):
        transactions.check("pectra", 1, _set_code(2**64 - 1))


def test_fee_market_nonce_above_64_bits() -> None:
    """A type 2 transaction holds its nonce in 256 bits, so a nonce of 2^64 decodes."""
    message = "nonceOverflow (nonce := 18446744073709551616)"
    with raises(transactions.TransactionError, message):
        transactions.check("pectra", 1, _fee_market(2**64))
