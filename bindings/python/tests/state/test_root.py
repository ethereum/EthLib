"""The state root against the genesis tests of ethereum/tests.

Each case of `genesis/basic_genesis_tests.json` gives an allocation
and the RLP of its genesis block.
The state root of the allocation must be the fourth field of the block header.
`genesis/README.md` gives the origin of the file and its licence.
"""

import json
from pathlib import Path

import pytest

from ethlib.state import state_root

_CASES = json.loads(
    (Path(__file__).resolve().parent / "genesis" / "basic_genesis_tests.json").read_text()
)

# The root of the empty trie: the Keccak-256 hash of `0x80`.
EMPTY_TRIE_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")


def _length_prefix(offset: int, length: int) -> bytes:
    if length < 56:
        return bytes([offset + length])
    size = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(size)]) + size


def rlp_encode(item: bytes | int | list) -> bytes:
    """The RLP encoding of a byte string, a scalar or a list of items."""
    if isinstance(item, int):
        item = item.to_bytes((item.bit_length() + 7) // 8, "big")
    if isinstance(item, bytes):
        if len(item) == 1 and item[0] < 0x80:
            return item
        return _length_prefix(0x80, len(item)) + item
    payload = b"".join(rlp_encode(x) for x in item)
    return _length_prefix(0xC0, len(payload)) + payload


def _rlp_split(data: bytes) -> tuple[bool, bytes, bytes]:
    """The first item of `data`: whether it is a list, its payload, and the bytes after it."""
    first = data[0]
    if first < 0x80:
        return False, data[:1], data[1:]
    is_list = first >= 0xC0
    short = first - (0xC0 if is_list else 0x80)
    if short < 56:
        start, length = 1, short
    else:
        size = short - 55
        start, length = 1 + size, int.from_bytes(data[1 : 1 + size], "big")
    return is_list, data[start : start + length], data[start + length :]


def _rlp_list(payload: bytes) -> list[bytes]:
    """The encodings of the items of a list payload."""
    items = []
    while payload:
        _, _, rest = _rlp_split(payload)
        items.append(payload[: len(payload) - len(rest)])
        payload = rest
    return items


def header_state_root(block: bytes) -> bytes:
    """The state root of a block: the fourth field of its header, the first item of the block."""
    _, block_payload, _ = _rlp_split(block)
    _, header_payload, _ = _rlp_split(block_payload)
    _, root, _ = _rlp_split(_rlp_list(header_payload)[3])
    return root


def _int(value: str) -> int:
    return int(value, 16) if value.startswith("0x") else int(value)


def encode_alloc(alloc: dict) -> bytes:
    """The RLP form of an allocation that the binding reads."""
    accounts = []
    for address, account in alloc.items():
        storage = [
            [_int(key).to_bytes(32, "big"), _int(value)]
            for key, value in account.get("storage", {}).items()
        ]
        accounts.append(
            [
                bytes.fromhex(address.removeprefix("0x")),
                _int(account.get("nonce", "0")),
                _int(account.get("balance", account.get("wei", "0"))),
                bytes.fromhex(account.get("code", "0x").removeprefix("0x")),
                storage,
            ]
        )
    return rlp_encode(accounts)


@pytest.mark.parametrize("name", sorted(_CASES))
def test_genesis_state_root(name: str) -> None:
    case = _CASES[name]
    expected = header_state_root(bytes.fromhex(case["result"]))
    assert state_root(encode_alloc(case["alloc"])) == expected


def test_empty_state() -> None:
    assert state_root(rlp_encode([])) == EMPTY_TRIE_ROOT


ADDRESS_A = bytes.fromhex("9ca0e998df92c5351cecbbb6dba82ac2266f7e0c")
ADDRESS_B = bytes.fromhex("cd2a3d9f938e13cd947ec05abc7fe734df8dd826")


def test_order_of_accounts_and_slots() -> None:
    # The root depends on the entries, not on the order in which they are given.
    slots = [[(3).to_bytes(32, "big"), 7], [(4).to_bytes(32, "big"), 8]]
    a = [ADDRESS_A, 1, 2, b"\x60\x00", slots]
    b = [ADDRESS_B, 0, 10**21, b"", []]
    a_reversed = [ADDRESS_A, 1, 2, b"\x60\x00", slots[::-1]]
    assert state_root(rlp_encode([a, b])) == state_root(rlp_encode([b, a_reversed]))


def test_zero_slot_is_absent() -> None:
    with_zero = [ADDRESS_A, 0, 0, b"", [[(3).to_bytes(32, "big"), 0]]]
    without = [ADDRESS_A, 0, 0, b"", []]
    assert state_root(rlp_encode([with_zero])) == state_root(rlp_encode([without]))


def test_rejects_repeated_address() -> None:
    account = [ADDRESS_A, 0, 0, b"", []]
    with pytest.raises(ValueError, match="given twice"):
        state_root(rlp_encode([account, account]))


ACCOUNT_ERROR = "an account is not a list of address, nonce, balance, code and storage"


@pytest.mark.parametrize(
    "state, error",
    [
        (b"", "state is not one RLP item"),
        (rlp_encode(b"\x01\x02"), "state is not an RLP list"),
        (rlp_encode([[ADDRESS_A, 0, 0, b""]]), ACCOUNT_ERROR),
        (rlp_encode([[ADDRESS_A[:19], 0, 0, b"", []]]), ACCOUNT_ERROR),
        (rlp_encode([[ADDRESS_A, 0, 2**256, b"", []]]), ACCOUNT_ERROR),
        (rlp_encode([[ADDRESS_A, 0, 0, b"", [[b"\x03", 7]]]]), ACCOUNT_ERROR),
    ],
)
def test_rejects_malformed_state(state: bytes, error: str) -> None:
    with pytest.raises(ValueError, match=error):
        state_root(state)


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        state_root("abc")  # ty: ignore[invalid-argument-type]
