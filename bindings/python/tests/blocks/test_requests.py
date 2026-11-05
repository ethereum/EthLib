"""Deposit requests and the requests hash against the Prague blockchain tests of execution-specs."""

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from ethlib.serialization import rlp

_REPO = Path(__file__).resolve().parents[4]
_CASES_FILE = _REPO / "tests" / "execution" / "blocks" / "deposits.json"
CASES = json.loads(_CASES_FILE.read_text())

DEPOSIT_CONTRACT = bytes.fromhex("00000000219ab540356cbb839cbe05303d7705fa")
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
    deposits = blocks.deposit_requests(_logs(case["logs"]))
    # The withdrawal and consolidation queues of these tests are empty,
    # so their lists hold only a type.
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


def test_request_is_the_five_fields() -> None:
    data = _deposit_log_data()
    request = blocks.deposit_requests(_deposit_log(data))
    # The public key, credentials, amount, signature and index follow their sizes in the log.
    fields = [(160, 48), (256, 32), (320, 8), (384, 96), (512, 8)]
    assert request == b"".join(data[o + 32 : o + 32 + s] for o, s in fields)
    assert len(request) == 192


def _word(value: int) -> bytes:
    return value.to_bytes(32, "big")


@pytest.mark.parametrize(
    "position, value, code",
    [
        (0, 161, 302),  # the offset of the public key
        (128, 544, 302),  # the offset of the index
        (160, 47, 303),  # the size of the public key
        (512, 9, 303),  # the size of the index
    ],
)
def test_wrong_layout_rejected(position: int, value: int, code: int) -> None:
    data = bytearray(_deposit_log_data())
    data[position : position + 32] = _word(value)
    with pytest.raises(blocks.BlockError) as error:
        blocks.deposit_requests(_deposit_log(bytes(data)))
    assert error.value.code == code


def test_wrong_length_rejected() -> None:
    with pytest.raises(blocks.BlockError) as error:
        blocks.deposit_requests(_deposit_log(_deposit_log_data() + b"\x00"))
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
    assert blocks.deposit_requests(other) == b""


def test_requests_hash_skips_lists_without_data() -> None:
    def expected(requests: list) -> bytes:
        inner = b"".join(hashlib.sha256(r).digest() for r in requests if len(r) > 1)
        return hashlib.sha256(inner).digest()

    for requests in [[], [b"\x00"], [b"\x00", b"\x01ab", b"\x02"], [b"\x00xy", b"\x01", b"\x02z"]]:
        assert blocks.requests_hash(rlp.encode(requests)) == expected(requests)
