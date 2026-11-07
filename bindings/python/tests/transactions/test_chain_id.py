"""The chain ID of a typed transaction, a 64-bit number."""

# The execution test suites hold no typed transaction with a chain ID of 2^64 or more.
# So each case here is built and signed in the test.

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import address, sign
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

KEY = bytes(31) + b"\x01"
OTHER = b"\x11" * 20
# The error of a first field of 2^64, read as a scalar below 2^64.
TOO_LARGE = "decoding: field 0: scalarTooLarge 18446744073709551616 64"


def _int(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _fee_market(chain_id: int, nonce: int = 0) -> bytes:
    """A signed type 2 transfer of the key's account on the chain `chain_id`."""
    fields = [_int(chain_id), _int(nonce), _int(1), _int(10), _int(21000), OTHER, _int(1), b"", []]
    signature = sign(KEY, keccak256(b"\x02" + rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return b"\x02" + rlp.encode(fields + [_int(v), r.lstrip(b"\0"), s.lstrip(b"\0")])


def test_largest_chain_id() -> None:
    """A chain ID of 2^64 - 1 decodes, and the transaction is valid on that chain."""
    checked = transactions.check("pectra", 2**64 - 1, _fee_market(2**64 - 1))
    assert checked.sender == address(KEY)
    assert checked.intrinsic_gas == 21000


def test_chain_id_above_64_bits() -> None:
    """A chain ID of 2^64 does not fit 64 bits, so the transaction fails to decode."""
    with raises(transactions.TransactionError, TOO_LARGE) as error:
        transactions.check("pectra", 1, _fee_market(2**64))
    # The code of a decoding error.
    assert error.value.code == 3


def test_chain_id_is_decoded_first() -> None:
    """With a nonce of 2^256 too, the error names the chain ID, the first field."""
    with raises(transactions.TransactionError, TOO_LARGE):
        transactions.check("pectra", 1, _fee_market(2**64, nonce=2**256))
