"""Withdrawals against the Shanghai blockchain tests of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.serialization import rlp
from ethlib.state import StateError, state_root, withdrawals_root
from raising import raises

_REPO = Path(__file__).resolve().parents[4]
_CASES_FILE = _REPO / "tests" / "execution" / "blocks" / "withdrawals.json"
CASES = json.loads(_CASES_FILE.read_text())


def _scalar(value: str) -> bytes:
    number = int(value, 16)
    return number.to_bytes((number.bit_length() + 7) // 8, "big")


def _state(pre: dict) -> bytes:
    """The RLP input of the state export: each account as address, nonce, balance, code, storage."""
    accounts = []
    for address, account in pre.items():
        storage = [
            [int(key, 16).to_bytes(32, "big"), _scalar(value)]
            for key, value in account["storage"].items()
        ]
        accounts.append(
            [
                bytes.fromhex(address[2:]),
                _scalar(account["nonce"]),
                _scalar(account["balance"]),
                bytes.fromhex(account["code"][2:]),
                storage,
            ]
        )
    return rlp.encode(accounts)


def _case_id(case) -> str:
    return case["test"].split("::")[-1][:90]


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_withdrawals_post_state(case) -> None:
    state = _state(case["pre"])
    # The state before the block has the root of the genesis header.
    assert state_root(state) == bytes.fromhex(case["preStateRoot"])
    # A block with withdrawals and no transaction has the root of its header after them.
    block = bytes.fromhex(case["rlp"])
    assert withdrawals_root("shapella", state, block) == bytes.fromhex(case["postStateRoot"])


def test_cases_cover_the_edges() -> None:
    blocks = [rlp.decode(bytes.fromhex(c["rlp"])) for c in CASES]
    amounts = [int.from_bytes(w[3], "big") for b in blocks for w in b[3]]
    # Zero amounts, the largest amount, and an address with many withdrawals all appear.
    assert 0 in amounts and 2**64 - 1 in amounts
    assert any(len(b[3]) != len({w[2] for w in b[3]}) for b in blocks)


def test_withdrawals_change_the_root() -> None:
    case = next(c for c in CASES if rlp.decode(bytes.fromhex(c["rlp"]))[3])
    state = _state(case["pre"])
    assert withdrawals_root("shapella", state, bytes.fromhex(case["rlp"])) != state_root(state)


def test_shapella_block_rejected_at_paris() -> None:
    # A Paris block has no withdrawals field, so a Shapella block does not decode at Paris.
    case = CASES[0]
    with raises(
        StateError, "block rejected: EthLib.Serialization.Rlp.RlpError.wrongFieldCount 3 4"
    ) as error:
        withdrawals_root("paris", _state(case["pre"]), bytes.fromhex(case["rlp"]))
    assert error.value.code == 0


def test_fork_before_shapella_rejected() -> None:
    # A Paris block decodes at Paris, but Paris has no withdrawals.
    blocks = json.loads((_CASES_FILE.parent / "blockchain_tests.json").read_text())
    paris = next(c for c in blocks if c["network"] == "Paris")
    with raises(StateError, "the fork is before Shapella") as error:
        withdrawals_root("paris", _state(CASES[0]["pre"]), bytes.fromhex(paris["rlp"]))
    assert error.value.code == 0
