"""The eth session: message order, pending requests and transaction resends."""

import pytest

from ethlib.execution.network import (
    BLOCK_RANGE_UPDATE,
    GET_POOLED_TRANSACTIONS,
    GET_RECEIPTS,
    NEW_BLOCK,
    NEW_BLOCK_HASHES,
    POOLED_TRANSACTIONS,
    RECEIPTS,
    STATUS,
    TRANSACTIONS,
    EthWireError,
    session,
)
from ethlib.networking import forkid
from ethlib.networking.forkid import BLOCK
from ethlib.serialization import rlp
from raising import raises

# The rules come from caps/eth.md of ethereum/devp2p at commit 88f1c808.
# The sections are "Basic Operation", "Protocol Messages" and "Transactions (0x02)".
# No official vectors exist, so each message is RLP built here.

GENESIS = bytes.fromhex("d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3")
LATEST_HASH = bytes(range(32))

# The chain of EIP-2124 "Test Cases": mainnet up to Petersburg.
SCHEDULE = forkid.schedule(
    GENESIS,
    0,
    [
        ("frontier", BLOCK, 0),
        ("homestead", BLOCK, 1_150_000),
        ("daoFork", BLOCK, 1_920_000),
        ("tangerineWhistle", BLOCK, 2_463_000),
        ("spuriousDragon", BLOCK, 2_675_000),
        ("byzantium", BLOCK, 4_370_000),
        ("petersburg", BLOCK, 7_280_000),
    ],
)
HEAD = 7_987_396
# The identifier of that chain at HEAD, from EIP-2124 "Test Cases".
FORK_ID = (bytes.fromhex("668db0af"), b"")
# A fork identifier that EIP-2124 rejects at HEAD: an unknown hash.
BAD_FORK_ID = (bytes.fromhex("deadbeef"), b"")

SENT = True
RECEIVED = False

# Two RLP lists that stand for transactions; the session reads only their hashes.
TX0 = (b"\x00", b"\x01")
TX3 = (b"\x03", b"\x04")


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _status(fork_id: tuple[bytes, bytes] = FORK_ID, earliest: int = 0) -> bytes:
    return rlp.encode([_p(69), _p(1), GENESIS, list(fork_id), _p(earliest), _p(HEAD), LATEST_HASH])


def _get_receipts(request_id: int) -> bytes:
    return rlp.encode([_p(request_id), [LATEST_HASH]])


def _receipts(request_id: int) -> bytes:
    return rlp.encode([_p(request_id), [[]]])


def _transactions(*txs: tuple[bytes, bytes]) -> bytes:
    return rlp.encode([list(tx) for tx in txs])


def _run(*events: tuple[bool, int, bytes]) -> list[tuple[str, int]]:
    return session(69, SCHEDULE, HEAD, 0, events)


STATUS_IN = (RECEIVED, STATUS, _status())
STATUS_OUT = (SENT, STATUS, _status())


def test_request_response_and_resends() -> None:
    # Both Status messages open the session, and a response closes the request it answers.
    assert _run(
        STATUS_OUT,
        STATUS_IN,
        (SENT, GET_RECEIPTS, _get_receipts(7)),
        (RECEIVED, RECEIPTS, _receipts(7)),
        (RECEIVED, TRANSACTIONS, _transactions(TX3)),
        (SENT, TRANSACTIONS, _transactions(TX3)),
        (SENT, TRANSACTIONS, _transactions(TX0)),
        (SENT, TRANSACTIONS, _transactions(TX0)),
    ) == [
        ("sent", 0),
        ("accept", 0),
        ("sent", 1),
        ("accept", 0),
        ("accept", 0),
        # The peer sent this transaction, so it must not go back.
        ("refused", 0),
        ("sent", 0),
        # This node sent it already in this session.
        ("refused", 0),
    ]


def test_send_before_status() -> None:
    # Only Status may go out before both Status messages have passed.
    assert _run(
        (SENT, GET_RECEIPTS, _get_receipts(7)),
        STATUS_IN,
        (SENT, TRANSACTIONS, _transactions(TX0)),
        STATUS_OUT,
        (SENT, TRANSACTIONS, _transactions(TX0)),
    ) == [("refused", 0), ("accept", 0), ("refused", 0), ("sent", 0), ("sent", 0)]


def test_message_before_status() -> None:
    with raises(EthWireError, "event 0: message came before the peer's Status") as info:
        _run((RECEIVED, TRANSACTIONS, _transactions(TX0)))
    assert info.value.code == 701


def test_unsolicited_response() -> None:
    with raises(
        EthWireError, "event 3: response with request ID 9 answers no pending request"
    ) as info:
        _run(
            STATUS_OUT,
            STATUS_IN,
            (SENT, GET_RECEIPTS, _get_receipts(7)),
            (RECEIVED, RECEIPTS, _receipts(9)),
        )
    assert info.value.code == 703


def test_response_of_another_type() -> None:
    # The request ID matches, but PooledTransactions does not answer GetReceipts.
    with raises(
        EthWireError, "event 3: response with request ID 7 answers no pending request"
    ) as info:
        _run(
            STATUS_OUT,
            STATUS_IN,
            (SENT, GET_RECEIPTS, _get_receipts(7)),
            (RECEIVED, POOLED_TRANSACTIONS, rlp.encode([_p(7), [list(TX3)]])),
        )
    assert info.value.code == 703


def test_response_answers_once() -> None:
    with raises(
        EthWireError, "event 4: response with request ID 7 answers no pending request"
    ) as info:
        _run(
            STATUS_OUT,
            STATUS_IN,
            (SENT, GET_RECEIPTS, _get_receipts(7)),
            (RECEIVED, RECEIPTS, _receipts(7)),
            (RECEIVED, RECEIPTS, _receipts(7)),
        )
    assert info.value.code == 703


def test_second_status() -> None:
    with raises(EthWireError, "event 1: a second Status came in an active session") as info:
        _run(STATUS_IN, STATUS_IN)
    assert info.value.code == 702


def test_bad_status() -> None:
    with raises(
        EthWireError,
        "event 0: fork identifier refused: chains are incompatible, or the local node is stale",
    ) as info:
        _run((RECEIVED, STATUS, _status(BAD_FORK_ID)))
    assert info.value.code == 102


def test_status_with_bad_range() -> None:
    message = f"event 0: block range starts at {HEAD + 1}, after its end {HEAD}"
    with raises(EthWireError, message) as info:
        _run((RECEIVED, STATUS, _status(earliest=HEAD + 1)))
    assert info.value.code == 103


def test_block_range_update() -> None:
    good = rlp.encode([b"", _p(HEAD), LATEST_HASH])
    bad = rlp.encode([_p(HEAD + 1), _p(HEAD), LATEST_HASH])
    assert _run(STATUS_IN, (RECEIVED, BLOCK_RANGE_UPDATE, good)) == [("accept", 0), ("accept", 0)]
    message = f"event 1: block range starts at {HEAD + 1}, after its end {HEAD}"
    with raises(EthWireError, message) as info:
        _run(STATUS_IN, (RECEIVED, BLOCK_RANGE_UPDATE, bad))
    assert info.value.code == 704


@pytest.mark.parametrize(
    "message_id, data",
    [
        (NEW_BLOCK_HASHES, rlp.encode([[LATEST_HASH, _p(HEAD)]])),
        (NEW_BLOCK, rlp.encode([[], _p(1)])),
    ],
)
def test_block_announcements_discarded(message_id: int, data: bytes) -> None:
    assert _run(STATUS_IN, (RECEIVED, message_id, data)) == [("accept", 0), ("discard", 0)]


def test_empty_or_duplicate_transactions_refused() -> None:
    assert _run(
        STATUS_OUT,
        STATUS_IN,
        (SENT, TRANSACTIONS, _transactions()),
        (SENT, TRANSACTIONS, _transactions(TX0, TX0)),
    ) == [("sent", 0), ("accept", 0), ("refused", 0), ("refused", 0)]


def test_pooled_transactions_never_refused() -> None:
    pooled = rlp.encode([_p(5), [list(TX3)]])
    # Sending the answer to a request never refuses, even for a transaction the peer sent.
    assert _run(
        STATUS_OUT,
        STATUS_IN,
        (RECEIVED, TRANSACTIONS, _transactions(TX3)),
        (SENT, POOLED_TRANSACTIONS, pooled),
    ) == [("sent", 0), ("accept", 0), ("accept", 0), ("sent", 0)]


def test_pooled_answer_counts_as_sent() -> None:
    pooled = rlp.encode([_p(5), [list(TX0)]])
    # A transaction sent in an answer must not go out again in Transactions.
    assert _run(
        STATUS_OUT,
        STATUS_IN,
        (SENT, POOLED_TRANSACTIONS, pooled),
        (SENT, TRANSACTIONS, _transactions(TX0)),
    ) == [("sent", 0), ("accept", 0), ("sent", 0), ("refused", 0)]


def test_received_pooled_transactions_are_known() -> None:
    get_pooled = rlp.encode([_p(5), [LATEST_HASH]])
    pooled = rlp.encode([_p(5), [list(TX3)]])
    assert _run(
        STATUS_OUT,
        STATUS_IN,
        (SENT, GET_POOLED_TRANSACTIONS, get_pooled),
        (RECEIVED, POOLED_TRANSACTIONS, pooled),
        (SENT, TRANSACTIONS, _transactions(TX3)),
    ) == [("sent", 0), ("accept", 0), ("sent", 1), ("accept", 0), ("refused", 0)]


@pytest.mark.parametrize("direction", [SENT, RECEIVED])
def test_malformed_message(direction: bool) -> None:
    with raises(EthWireError, "event 1: message data is not RLP of the expected shape") as info:
        _run(STATUS_IN, (direction, TRANSACTIONS, b"\x01"))
    assert info.value.code == 2


def test_unknown_version() -> None:
    with raises(EthWireError, "eth/67 is not a version that EthLib specifies") as info:
        session(67, SCHEDULE, HEAD, 0, [])
    assert info.value.code == 0
