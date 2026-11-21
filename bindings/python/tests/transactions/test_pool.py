"""The rules by which a node keeps a transaction from a peer in its pool, at Prague."""

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import address, sign
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

KEY = bytes(31) + b"\x01"
OTHER = b"\x11" * 20
GWEI = 10**9
ETHER = 10**18
UNSUPPORTED_TYPE = 2
NONCE_TOO_LOW = 205
INSUFFICIENT_BALANCE = 207


def _int(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _signed(type_: int, fields: list) -> bytes:
    """A typed transaction with its fields, signed by the key."""
    signature = sign(KEY, keccak256(bytes([type_]) + rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return bytes([type_]) + rlp.encode(fields + [_int(v), r.lstrip(b"\0"), s.lstrip(b"\0")])


def _fee_market(nonce: int) -> bytes:
    """A type 2 transfer of 0.5 ether, gas limit 21000 and most fee 10 gwei, on chain 1."""
    fields = [_int(1), _int(nonce), _int(GWEI), _int(10 * GWEI), _int(21_000), OTHER]
    return _signed(2, fields + [_int(ETHER // 2), b"", []])


def _blob(nonce: int) -> bytes:
    """A type 3 transaction with one blob hash, gas limit 21000, on chain 1."""
    versioned = b"\x01" + bytes(31)
    fields = [_int(1), _int(nonce), _int(GWEI), _int(10 * GWEI), _int(21_000), OTHER]
    return _signed(3, fields + [b"", b"", [], _int(1), [versioned]])


# The sender holds 1 ether, with nonce 5 and no code.
STATE = rlp.encode([[address(KEY), _int(5), _int(ETHER), b"", []]])


def test_future_nonce_kept() -> None:
    """A nonce above the sender's is kept, and the transaction may go whole to peers."""
    assert transactions.admit_to_pool("pectra", 1, _fee_market(7), STATE) == (address(KEY), True)


def test_low_nonce_discarded() -> None:
    """A nonce below the sender's is refused, and the peer is kept."""
    with raises(transactions.TransactionError, "nonceTooLow (expected := 5) (nonce := 4)") as e:
        transactions.admit_to_pool("pectra", 1, _fee_market(4), STATE)
    assert e.value.code == NONCE_TOO_LOW


def test_unknown_type_refused() -> None:
    """A transaction of type 7 has a type that no fork defines, so it does not even decode."""
    with raises(transactions.TransactionError, "unsupportedType (type := 7)") as e:
        transactions.admit_to_pool("pectra", 1, b"\x07" + rlp.encode([]), STATE)
    assert e.value.code == UNSUPPORTED_TYPE


def test_poor_sender_discarded() -> None:
    """A sender with 0.5 ether cannot pay 0.5 ether and the gas at the most fee."""
    poor = rlp.encode([[address(KEY), _int(5), _int(ETHER // 2), b"", []]])
    cost = ETHER // 2 + 21_000 * 10 * GWEI
    message = f"insufficientBalance (balance := {ETHER // 2}) (cost := {cost})"
    with raises(transactions.TransactionError, message) as e:
        transactions.admit_to_pool("pectra", 1, _fee_market(5), poor)
    assert e.value.code == INSUFFICIENT_BALANCE


def test_blob_kept_not_sent_whole() -> None:
    """A blob transaction passes the same checks, but is only announced by its hash."""
    assert transactions.admit_to_pool("pectra", 1, _blob(5), STATE) == (address(KEY), False)
