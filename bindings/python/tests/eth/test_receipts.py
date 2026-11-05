"""The receipts of the eth capability, against the receipts of the blockchain tests.

The receipts come from tests/execution/blocks/receipts.json, pinned as its README says.
Each one is sent as eth/68 and eth/69 send it, and checked against the root of a block that holds
it alone.
The messages are built here as RLP, from caps/eth.md, EIP-7642 and EIP-7975.
"""

import pytest

from ethlib.execution import trie
from ethlib.execution.network import (
    GET_RECEIPTS,
    RECEIPTS,
    EthWireError,
    decode_message,
    receipts_match,
)
from ethlib.serialization import rlp

from blocks.test_blocks import FORK_OF_NETWORK
from blocks.test_receipts import CASES, _case_id


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _consensus(case) -> bytes:
    return bytes.fromhex(case["rlp"])


def _fields(case) -> list:
    """The four fields of the consensus receipt: outcome, gas, bloom and logs."""
    receipt = _consensus(case)
    return rlp.decode(receipt if receipt[0] >= 0xC0 else receipt[1:])


def _eth68(case):
    """The receipt as eth/68 sends it: a legacy one as its list, a typed one as bytes."""
    receipt = _consensus(case)
    return rlp.decode(receipt) if receipt[0] >= 0xC0 else receipt


def _eth69(case) -> list:
    """The receipt as eth/69 sends it: the type first, and no Bloom filter."""
    outcome, gas, _bloom, logs = _fields(case)
    return [_p(int(case["type"], 16)), outcome, gas, logs]


def _root(case) -> bytes:
    # The receipts root of a block whose one receipt is this one: the key is RLP of index 0.
    return trie.root([(rlp.encode(b""), _consensus(case))])


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_receipts_match(case) -> None:
    fork = FORK_OF_NETWORK[case["network"]]
    root = _root(case)
    assert receipts_match(68, fork, root, rlp.encode([_eth68(case)]))
    for version in (69, 70, 71, 72):
        assert receipts_match(version, fork, root, rlp.encode([_eth69(case)]))
    # A receipt in the other form does not read.
    assert not receipts_match(69, fork, root, rlp.encode([_eth68(case)]))


def test_wrong_root() -> None:
    case = CASES[0]
    fork = FORK_OF_NETWORK[case["network"]]
    assert not receipts_match(69, fork, bytes(32), rlp.encode([_eth69(case)]))


def test_logs_changed() -> None:
    # Another log changes the filter and the root, so the receipt no longer matches.
    case = next(c for c in CASES if c["logs"] > 0)
    fork = FORK_OF_NETWORK[case["network"]]
    wire = _eth69(case)
    wire[3] = wire[3][1:]
    assert not receipts_match(69, fork, _root(case), rlp.encode([wire]))


def test_fork_not_specified() -> None:
    with pytest.raises(EthWireError) as info:
        receipts_match(69, "hegota", bytes(32), rlp.encode([]))
    assert info.value.code == 0


HASHES = [bytes([i]) * 32 for i in (1, 2)]
LISTS = [[[_p(2), _p(1), _p(21000), []]], []]


@pytest.mark.parametrize(
    "version, message_id, data",
    [
        (68, GET_RECEIPTS, rlp.encode([_p(5), HASHES])),
        (69, GET_RECEIPTS, rlp.encode([_p(5), HASHES])),
        (70, GET_RECEIPTS, rlp.encode([_p(5), _p(3), HASHES])),
        (72, GET_RECEIPTS, rlp.encode([_p(5), b"", HASHES])),
        (69, RECEIPTS, rlp.encode([_p(5), LISTS])),
        (70, RECEIPTS, rlp.encode([_p(5), _p(1), LISTS])),
        (71, RECEIPTS, rlp.encode([_p(5), b"", LISTS])),
    ],
)
def test_round_trip(version: int, message_id: int, data: bytes) -> None:
    assert decode_message(version, message_id, data) == data


@pytest.mark.parametrize(
    "version, message_id, data",
    [
        # eth/70 adds the first receipt index, and eth/69 has none.
        (69, GET_RECEIPTS, rlp.encode([_p(5), _p(3), HASHES])),
        (70, GET_RECEIPTS, rlp.encode([_p(5), HASHES])),
        # lastBlockIncomplete is a flag, 0 or 1.
        (70, RECEIPTS, rlp.encode([_p(5), _p(2), LISTS])),
    ],
)
def test_wrong_form(version: int, message_id: int, data: bytes) -> None:
    with pytest.raises(EthWireError) as info:
        decode_message(version, message_id, data)
    assert info.value.code == 2
