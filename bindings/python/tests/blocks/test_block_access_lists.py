"""Block access lists against the EIP-7928 tests of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks

_FILE = Path(__file__).resolve().parents[4] / "tests" / "execution" / "blocks"
CASES = json.loads((_FILE / "block_access_lists.json").read_text())

VALID = [c for c in CASES if c["error"] is None]
INVALID = [c for c in CASES if c["error"] is not None]

# The tests whose payloads break a rule of the form of the list: order, uniqueness or empty slots.
FORM = {"test_bal_invalid_ordering", "test_bal_invalid_duplicate_entries",
        "test_bal_invalid_empty_slot_changes", "test_bal_invalid_account_order",
        "test_bal_invalid_duplicate_account"}
# The tests whose payloads hold bytes that are no RLP form of a list.
ENCODING = {"test_bal_invalid_non_minimal_scalar_encoding",
            "test_bal_invalid_engine_payload_encoding"}
# The codes of the rules of the form: order, uniqueness and empty slots.
FORM_CODES = range(401, 410)
TOO_MANY_ITEMS = 410

# The hash of the empty list, the Keccak-256 hash of 0xc0, as EIP-7928 gives it.
EMPTY_HASH = "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"


def _function(case) -> str:
    return case["test"].split("::")[-1].split("[")[0]


def _id(case) -> str:
    return f"{case['test'].split('[')[-1][:70]}-{case['payload']}"


@pytest.mark.parametrize("case", VALID, ids=_id)
def test_valid_list(case) -> None:
    bal = bytes.fromhex(case["bal"])
    # The hash is the one that the header of the block holds.
    assert blocks.block_access_list_hash(bal).hex() == case["hash"]
    blocks.check_block_access_list(bal, case["gasLimit"])


@pytest.mark.parametrize("case", [c for c in INVALID if _function(c) in FORM], ids=_id)
def test_form_rejected(case) -> None:
    with pytest.raises(blocks.BlockError) as error:
        blocks.check_block_access_list(bytes.fromhex(case["bal"]), case["gasLimit"])
    assert error.value.code in FORM_CODES


@pytest.mark.parametrize("case", [c for c in INVALID if _function(c) in ENCODING], ids=_id)
def test_encoding_rejected(case) -> None:
    # The decoder rejects the bytes, so no hash exists.
    with pytest.raises(blocks.BlockError, match="block access list rejected"):
        blocks.block_access_list_hash(bytes.fromhex(case["bal"]))


@pytest.mark.parametrize(
    "case", [c for c in INVALID if c["error"].endswith("BLOCK_ACCESS_LIST_GAS_LIMIT_EXCEEDED")],
    ids=_id)
def test_too_many_items(case) -> None:
    with pytest.raises(blocks.BlockError) as error:
        blocks.check_block_access_list(bytes.fromhex(case["bal"]), case["gasLimit"])
    assert error.value.code == TOO_MANY_ITEMS


def test_cases_cover_each_kind() -> None:
    assert len(VALID) == 1146
    assert sum(_function(c) in FORM for c in INVALID) == 17
    assert sum(_function(c) in ENCODING for c in INVALID) == 18
    assert sum(c["error"].endswith("GAS_LIMIT_EXCEEDED") for c in INVALID) == 5


def test_empty_list() -> None:
    assert blocks.block_access_list_hash(b"\xc0").hex() == EMPTY_HASH
    blocks.check_block_access_list(b"\xc0", 0)


def test_size_boundary() -> None:
    # One account with no change is one item, so a gas limit of 2000 allows it and 1999 does not.
    account = bytes([0xDA, 0x94]) + bytes(20) + bytes([0xC0] * 5)
    bal = bytes([0xDB]) + account
    blocks.check_block_access_list(bal, 2000)
    with pytest.raises(blocks.BlockError) as error:
        blocks.check_block_access_list(bal, 1999)
    assert error.value.code == TOO_MANY_ITEMS
