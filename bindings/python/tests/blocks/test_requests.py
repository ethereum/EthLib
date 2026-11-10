"""Deposit requests and the requests hash against the Prague blockchain tests of execution-specs."""

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from ethlib.serialization import rlp
from raising import raises

_REPO = Path(__file__).resolve().parents[4]
_CASES_FILE = _REPO / "tests" / "execution" / "blocks" / "deposits.json"
CASES = json.loads(_CASES_FILE.read_text())

# The fixtures run with the deposit contract of mainnet, at the address of EIP-6110.
DEPOSIT_CONTRACT = bytes.fromhex("00000000219ab540356cbb839cbe05303d7705fa")
# The deposit contract of Sepolia, the `depositContractAddress` of its genesis file.
SEPOLIA_DEPOSIT_CONTRACT = bytes.fromhex("7f02c3e3c98b133055b8b348b2ac625669ed295d")
# The first topic of an ERC-20 `Transfer` event, which the Sepolia deposit contract also emits.
TRANSFER_TOPIC = bytes.fromhex("ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef")
DEPOSIT_TOPIC = bytes.fromhex("649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5")


def _logs(logs: list) -> bytes:
    """The RLP list of logs, each as address, topics and data."""
    return rlp.encode(
        [
            [
                bytes.fromhex(log["address"][2:]),
                [bytes.fromhex(t[2:]) for t in log["topics"]],
                bytes.fromhex(log["data"][2:]),
            ]
            for log in logs
        ]
    )


def _case_id(case) -> str:
    return f"{case['test'].split('::')[-1][:90]}-{case['block']}"


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_requests_hash_of_block(case) -> None:
    deposits = blocks.deposit_requests(DEPOSIT_CONTRACT, _logs(case["logs"]))
    # The withdrawal and consolidation queues of these tests are empty.
    # So their lists hold only a type.
    requests = [b"\x00" + deposits, b"\x01", b"\x02"]
    assert blocks.requests_hash(rlp.encode(requests)) == bytes.fromhex(case["requestsHash"])


def test_cases_cover_deposits_and_other_logs() -> None:
    logs = [log for c in CASES for log in c["logs"]]
    deposits = [
        log
        for log in logs
        if bytes.fromhex(log["address"][2:]) == DEPOSIT_CONTRACT
        and log["topics"][:1] == ["0x" + DEPOSIT_TOPIC.hex()]
    ]
    assert deposits and len(deposits) < len(logs)
    assert any(not c["logs"] for c in CASES)


def _deposit_log_data() -> bytes:
    """The data of the first deposit log of the fixtures."""
    for case in CASES:
        for log in case["logs"]:
            if bytes.fromhex(log["address"][2:]) == DEPOSIT_CONTRACT and log["topics"]:
                return bytes.fromhex(log["data"][2:])
    raise AssertionError("no deposit log")


def _deposit_log(data: bytes) -> bytes:
    return rlp.encode([[DEPOSIT_CONTRACT, [DEPOSIT_TOPIC], data]])


def _request_of(data: bytes) -> bytes:
    """The request of a deposit log: its public key, credentials, amount, signature and index."""
    # Each field follows its size in the log, at the offset of its head word.
    fields = [(160, 48), (256, 32), (320, 8), (384, 96), (512, 8)]
    return b"".join(data[o + 32 : o + 32 + s] for o, s in fields)


def test_request_is_the_five_fields() -> None:
    data = _deposit_log_data()
    assert blocks.deposit_requests(DEPOSIT_CONTRACT, _deposit_log(data)) == _request_of(data)
    assert len(_request_of(data)) == 192


def _word(value: int) -> bytes:
    return value.to_bytes(32, "big")


@pytest.mark.parametrize(
    "position, value, code, error",
    [
        (0, 161, 302, "wrongOffset 0 161"),  # the offset of the public key
        (128, 544, 302, "wrongOffset 4 544"),  # the offset of the index
        (160, 47, 303, "wrongSize 0 47"),  # the size of the public key
        (512, 9, 303, "wrongSize 4 9"),  # the size of the index
    ],
)
def test_wrong_layout_rejected(position: int, value: int, code: int, error: str) -> None:
    data = bytearray(_deposit_log_data())
    data[position : position + 32] = _word(value)
    message = f"deposit log rejected: EthLib.Execution.Blocks.DepositError.{error}"
    with raises(blocks.BlockError, message) as caught:
        blocks.deposit_requests(DEPOSIT_CONTRACT, _deposit_log(bytes(data)))
    assert caught.value.code == code


def test_wrong_length_rejected() -> None:
    with raises(
        blocks.BlockError,
        "deposit log rejected: EthLib.Execution.Blocks.DepositError.wrongLength 577",
    ) as error:
        blocks.deposit_requests(DEPOSIT_CONTRACT, _deposit_log(_deposit_log_data() + b"\x00"))
    assert error.value.code == 301


def test_other_logs_ignored() -> None:
    # A log of another address, or with another first topic, is no deposit, whatever its data.
    other = rlp.encode(
        [
            [b"\x01" * 20, [DEPOSIT_TOPIC], b"\x00"],
            [DEPOSIT_CONTRACT, [], b"\x00"],
            [DEPOSIT_CONTRACT, [b"\x02" * 32], b"\x00"],
        ]
    )
    assert blocks.deposit_requests(DEPOSIT_CONTRACT, other) == b""


def test_deposit_contract_of_the_chain() -> None:
    # The same deposit log counts only on a chain whose deposit contract emitted it.
    data = _deposit_log_data()
    log = _deposit_log(data)
    assert blocks.deposit_requests(DEPOSIT_CONTRACT, log) == _request_of(data)
    assert blocks.deposit_requests(SEPOLIA_DEPOSIT_CONTRACT, log) == b""


def test_other_event_of_the_deposit_contract_before_a_deposit() -> None:
    # The Sepolia deposit contract emits `Transfer` in addition to the deposit event, by EIP-6110.
    data = _deposit_log_data()
    logs = rlp.encode(
        [
            [SEPOLIA_DEPOSIT_CONTRACT, [TRANSFER_TOPIC, bytes(32), bytes(32)], bytes(32)],
            [SEPOLIA_DEPOSIT_CONTRACT, [DEPOSIT_TOPIC], data],
        ]
    )
    assert blocks.deposit_requests(SEPOLIA_DEPOSIT_CONTRACT, logs) == _request_of(data)


@pytest.mark.parametrize("address", [b"", bytes(19), bytes(21)], ids=["empty", "19", "21"])
def test_deposit_contract_of_wrong_length(address: bytes) -> None:
    with raises(blocks.BlockError, "the deposit contract address is not 20 bytes") as error:
        blocks.deposit_requests(address, rlp.encode([]))
    assert error.value.code == 0


def test_deposit_contract_not_bytes() -> None:
    # The configuration takes an address as hex text, but this function takes only its bytes.
    with raises(TypeError, "deposit_contract must be bytes"):
        blocks.deposit_requests("0x" + DEPOSIT_CONTRACT.hex(), rlp.encode([]))


def test_requests_hash_skips_lists_without_data() -> None:
    def expected(requests: list) -> bytes:
        inner = b"".join(hashlib.sha256(r).digest() for r in requests if len(r) > 1)
        return hashlib.sha256(inner).digest()

    for requests in [[], [b"\x00"], [b"\x00", b"\x01ab", b"\x02"], [b"\x00xy", b"\x01", b"\x02z"]]:
        assert blocks.requests_hash(rlp.encode(requests)) == expected(requests)
