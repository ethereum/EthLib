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
FORM = {
    "test_bal_invalid_ordering",
    "test_bal_invalid_duplicate_entries",
    "test_bal_invalid_empty_slot_changes",
    "test_bal_invalid_account_order",
    "test_bal_invalid_duplicate_account",
}
# The tests whose payloads hold bytes that are no RLP form of a list.
ENCODING = {
    "test_bal_invalid_non_minimal_scalar_encoding",
    "test_bal_invalid_engine_payload_encoding",
}
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
    "case",
    [c for c in INVALID if c["error"].endswith("BLOCK_ACCESS_LIST_GAS_LIMIT_EXCEEDED")],
    ids=_id,
)
def test_too_many_items(case) -> None:
    with pytest.raises(blocks.BlockError) as error:
        blocks.check_block_access_list(bytes.fromhex(case["bal"]), case["gasLimit"])
    assert error.value.code == TOO_MANY_ITEMS


# The tests whose payloads keep the form of a list but disagree with the block.
# They record an access that the block does not make, miss one that it makes, or carry a wrong
# value, so only executing the block can reject them.
EXECUTION = {
    "test_bal_cross_tx_coinbase_funds_sender",
    "test_bal_cross_tx_funding_chain",
    "test_bal_invalid_account",
    "test_bal_invalid_balance_value",
    "test_bal_invalid_coinbase_balance_value",
    "test_bal_invalid_complex_corruption",
    "test_bal_invalid_extraneous_coinbase",
    "test_bal_invalid_extraneous_entries",
    "test_bal_invalid_field_entries",
    "test_bal_invalid_hash_mismatch",
    "test_bal_invalid_missing_account",
    "test_bal_invalid_missing_coinbase",
    "test_bal_invalid_missing_created_code",
    "test_bal_invalid_missing_nonce",
    "test_bal_invalid_missing_pre_block_system_call_read",
    "test_bal_invalid_missing_request_predeploy_accesses",
    "test_bal_invalid_missing_storage_write",
    "test_bal_invalid_missing_system_contract_entry",
    "test_bal_invalid_missing_withdrawal_account",
    "test_bal_invalid_missing_withdrawal_account_empty_block",
    "test_bal_invalid_nonce_value",
    "test_bal_invalid_noop_storage_change",
    "test_bal_invalid_noop_system_call_write_as_change",
    "test_bal_invalid_noop_value_change",
    "test_bal_invalid_omitted_slot_change_at_index",
    "test_bal_invalid_phantom_read_on_request_predeploy",
    "test_bal_invalid_phantom_read_on_selfdestruct",
    "test_bal_invalid_storage_value",
    "test_bal_invalid_surplus_system_address_from_system_call",
    "test_bal_invalid_tx_order",
    "test_bal_invalid_withdrawal_balance_value",
}


# The payloads of those tests that also break the form: an extra or reordered entry lands out of
# order, or reads and writes one slot.
FORM_ALSO = {
    "test_bal_invalid_account",
    "test_bal_invalid_complex_corruption",
    "test_bal_invalid_tx_order",
}
FORM_ALSO_EXTRA = (
    "extra_account_access]",
    "extra_balance]",
    "extra_storage_write_touched]",
    "extra_storage_write_uninvolved_account]",
)


def _form_also(case) -> bool:
    """Whether a payload that needs execution also breaks the form of the list."""
    if _function(case) in FORM_ALSO:
        return True
    extra = _function(case) == "test_bal_invalid_extraneous_entries"
    return extra and case["test"].endswith(FORM_ALSO_EXTRA)


NEEDS_EXECUTION = [c for c in INVALID if _function(c) in EXECUTION]


def test_cases_cover_each_kind() -> None:
    assert len(VALID) == 1146
    assert sum(_function(c) in FORM for c in INVALID) == 17
    assert sum(_function(c) in ENCODING for c in INVALID) == 18
    assert sum(c["error"].endswith("GAS_LIMIT_EXCEEDED") for c in INVALID) == 5
    # Every other invalid case belongs to a test that needs block execution, so a new kind of
    # case that no test reads fails here.
    read = FORM | ENCODING
    rest = [
        c
        for c in INVALID
        if _function(c) not in read and not c["error"].endswith("GAS_LIMIT_EXCEEDED")
    ]
    assert rest == NEEDS_EXECUTION
    assert (len(rest), sum(map(_form_also, rest))) == (80, 15)


@pytest.mark.parametrize("case", NEEDS_EXECUTION, ids=_id)
def test_needs_execution(case) -> None:
    # The blockchain tests of the same names run each of these blocks in the parity suite.
    # EthLib rejects each block there, since its list differs from the one that the body builds.
    # Here the form check alone rejects exactly the payloads that also break the form.
    bal = bytes.fromhex(case["bal"])
    if _form_also(case):
        with pytest.raises(blocks.BlockError) as error:
            blocks.check_block_access_list(bal, case["gasLimit"])
        assert error.value.code in FORM_CODES
    else:
        blocks.check_block_access_list(bal, case["gasLimit"])


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
