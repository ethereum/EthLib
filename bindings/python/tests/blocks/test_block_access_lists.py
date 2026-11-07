"""Block access lists against the EIP-7928 tests of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from raising import raises

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


def _message(case) -> str:
    variant = case["test"].split("[")[-1].removeprefix("fork_Amsterdam-blockchain_test_engine")
    return _MESSAGES[_function(case), variant.strip("-]")]


_INVALID = "block access list invalid: EthLib.Execution.Blocks.BlockAccessList.Error."
_REJECTED = "block access list rejected: EthLib.Serialization.Rlp.RlpError."

# The message of each invalid payload that the checks reject, by test and variant.
_MESSAGES = {
    ("test_bal_gas_limit_boundary", "below_boundary-no_tx-no_cl_withdrawal"): (
        _INVALID + "tooManyItems 25 24"
    ),
    ("test_bal_gas_limit_boundary", "below_boundary-no_tx-with_cl_withdrawal"): (
        _INVALID + "tooManyItems 26 25"
    ),
    ("test_bal_gas_limit_boundary", "below_boundary-with_tx-no_cl_withdrawal"): (
        _INVALID + "tooManyItems 28 27"
    ),
    ("test_bal_gas_limit_boundary", "below_boundary-with_tx-with_cl_withdrawal"): (
        _INVALID + "tooManyItems 29 28"
    ),
    ("test_bal_gas_limit_boundary_storage_keys", "below_boundary"): (
        _INVALID + "tooManyItems 30 29"
    ),
    ("test_bal_invalid_account", ""): (
        _INVALID + "accountsNotAscending\n  #v[149, 209, 190, 149, 141, 34, 173, 242, 148, "
        "66, 140, 19, 204, 113, 216, 159, 243, 32, 191, 211]"
    ),
    ("test_bal_invalid_account_order", ""): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_complex_corruption", ""): (
        _INVALID + "balanceChangesNotAscending\n  #v[42, 220, 37, 102, 80, 24, 170, 31, 224, "
        "230, 188, 102, 109, 172, 143, 194, 105, 127, 249, 186]"
    ),
    ("test_bal_invalid_duplicate_account", ""): (
        _INVALID + "accountsNotAscending\n  #v[214, 111, 34, 76, 189, 47, 171, 178, 27, 23, "
        "187, 83, 197, 97, 24, 243, 47, 98, 235, 214]"
    ),
    ("test_bal_invalid_duplicate_entries", "duplicate_balance_change"): (
        _INVALID + "balanceChangesNotAscending\n  #v[118, 2, 197, 112, 212, 149, 140, 9, 91, "
        "37, 28, 169, 175, 40, 4, 117, 93, 199, 40, 35]"
    ),
    ("test_bal_invalid_duplicate_entries", "duplicate_code_change"): (
        _INVALID + "codeChangesNotAscending\n  #v[37, 102, 185, 152, 156, 82, 99, 91, 21, "
        "147, 152, 191, 110, 139, 213, 247, 160, 232, 150, 155]"
    ),
    ("test_bal_invalid_duplicate_entries", "duplicate_nonce_change"): (
        _INVALID + "nonceChangesNotAscending\n  #v[246, 195, 169, 237, 193, 175, 160, 173, "
        "91, 114, 14, 77, 66, 225, 67, 124, 67, 211, 179, 255]"
    ),
    ("test_bal_invalid_duplicate_entries", "duplicate_slot_change"): (
        _INVALID + "storageChangesNotAscending\n  #v[118, 2, 197, 112, 212, 149, 140, 9, 91, "
        "37, 28, 169, 175, 40, 4, 117, 93, 199, 40, 35]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000001#256"
    ),
    ("test_bal_invalid_duplicate_entries", "duplicate_storage_read"): (
        _INVALID + "readsNotAscending\n  #v[118, 2, 197, 112, 212, 149, 140, 9, 91, 37, 28, "
        "169, 175, 40, 4, 117, 93, 199, 40, 35]"
    ),
    ("test_bal_invalid_duplicate_entries", "duplicate_storage_slot"): (
        _INVALID + "slotsNotAscending\n  #v[118, 2, 197, 112, 212, 149, 140, 9, 91, 37, 28, "
        "169, 175, 40, 4, 117, 93, 199, 40, 35]"
    ),
    ("test_bal_invalid_duplicate_entries", "storage_key_in_both_changes_and_reads"): (
        _INVALID + "readAndWritten\n  #v[118, 2, 197, 112, 212, 149, 140, 9, 91, 37, 28, 169, "
        "175, 40, 4, 117, 93, 199, 40, 35]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000001#256"
    ),
    ("test_bal_invalid_empty_slot_changes", "demoted_noop"): (
        _INVALID + "slotWithoutChange\n  #v[116, 62, 234, 74, 91, 214, 37, 228, 5, 122, 43, "
        "11, 6, 228, 191, 86, 116, 59, 174, 36]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000000#256"
    ),
    ("test_bal_invalid_empty_slot_changes", "unrelated_slot"): (
        _INVALID + "slotWithoutChange\n  #v[23, 16, 152, 104, 233, 87, 55, 135, 79, 29, 90, "
        "237, 116, 100, 39, 141, 41, 23, 72, 37]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000001#256"
    ),
    (
        "test_bal_invalid_engine_payload_encoding",
        "header_commits_to_canonical_rlp-empty_byte_string",
    ): (_REJECTED + "inputTooShort 1 0"),
    ("test_bal_invalid_engine_payload_encoding", "header_commits_to_canonical_rlp-rlp_non_list"): (
        _REJECTED + "bytesAsList"
    ),
    (
        "test_bal_invalid_engine_payload_encoding",
        "header_commits_to_canonical_rlp-rlp_truncated_list",
    ): (_REJECTED + "inputTooShort 1 0"),
    (
        "test_bal_invalid_engine_payload_encoding",
        "header_commits_to_payload_rlp-empty_byte_string",
    ): (_REJECTED + "inputTooShort 1 0"),
    ("test_bal_invalid_engine_payload_encoding", "header_commits_to_payload_rlp-rlp_non_list"): (
        _REJECTED + "bytesAsList"
    ),
    (
        "test_bal_invalid_engine_payload_encoding",
        "header_commits_to_payload_rlp-rlp_truncated_list",
    ): (_REJECTED + "inputTooShort 1 0"),
    ("test_bal_invalid_extraneous_entries", "out_of_bounds-extra_account_access"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "out_of_bounds-extra_balance"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "out_of_bounds-extra_storage_write_touched"): (
        _INVALID + "readAndWritten\n  #v[41, 83, 111, 247, 58, 50, 236, 131, 154, 252, 215, "
        "21, 242, 17, 134, 127, 146, 199, 162, 191]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000000#256"
    ),
    (
        "test_bal_invalid_extraneous_entries",
        "out_of_bounds-extra_storage_write_uninvolved_account",
    ): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "same_tx-extra_account_access"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "same_tx-extra_balance"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "same_tx-extra_storage_write_touched"): (
        _INVALID + "readAndWritten\n  #v[41, 83, 111, 247, 58, 50, 236, 131, 154, 252, 215, "
        "21, 242, 17, 134, 127, 146, 199, 162, 191]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000000#256"
    ),
    ("test_bal_invalid_extraneous_entries", "same_tx-extra_storage_write_uninvolved_account"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "system_tx-extra_account_access"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "system_tx-extra_balance"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_extraneous_entries", "system_tx-extra_storage_write_touched"): (
        _INVALID + "readAndWritten\n  #v[41, 83, 111, 247, 58, 50, 236, 131, 154, 252, 215, "
        "21, 242, 17, 134, 127, 146, 199, 162, 191]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000000#256"
    ),
    ("test_bal_invalid_extraneous_entries", "system_tx-extra_storage_write_uninvolved_account"): (
        _INVALID + "accountsNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, 219, "
        "245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_canonical_rlp-field_balance",
    ): (
        _REJECTED + "inField\n  3\n  (EthLib.Serialization.Rlp.RlpError.inField 1 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_canonical_rlp-field_block_access_index",
    ): (
        _REJECTED + "inField\n  3\n  (EthLib.Serialization.Rlp.RlpError.inField 0 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_canonical_rlp-field_nonce",
    ): (
        _REJECTED + "inField\n  4\n  (EthLib.Serialization.Rlp.RlpError.inField 1 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_canonical_rlp-field_storage_read",
    ): (_REJECTED + "inField 2 (EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar)"),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_canonical_rlp-field_storage_slot",
    ): (
        _REJECTED + "inField\n  1\n  (EthLib.Serialization.Rlp.RlpError.inField 0 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_canonical_rlp-field_storage_value",
    ): (
        _REJECTED + "inField\n  1\n  (EthLib.Serialization.Rlp.RlpError.inField\n    1\n    "
        "(EthLib.Serialization.Rlp.RlpError.inField 1 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar)))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_payload_rlp-field_balance",
    ): (
        _REJECTED + "inField\n  3\n  (EthLib.Serialization.Rlp.RlpError.inField 1 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_payload_rlp-field_block_access_index",
    ): (
        _REJECTED + "inField\n  3\n  (EthLib.Serialization.Rlp.RlpError.inField 0 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    ("test_bal_invalid_non_minimal_scalar_encoding", "header_commits_to_payload_rlp-field_nonce"): (
        _REJECTED + "inField\n  4\n  (EthLib.Serialization.Rlp.RlpError.inField 1 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_payload_rlp-field_storage_read",
    ): (_REJECTED + "inField 2 (EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar)"),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_payload_rlp-field_storage_slot",
    ): (
        _REJECTED + "inField\n  1\n  (EthLib.Serialization.Rlp.RlpError.inField 0 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar))"
    ),
    (
        "test_bal_invalid_non_minimal_scalar_encoding",
        "header_commits_to_payload_rlp-field_storage_value",
    ): (
        _REJECTED + "inField\n  1\n  (EthLib.Serialization.Rlp.RlpError.inField\n    1\n    "
        "(EthLib.Serialization.Rlp.RlpError.inField 1 "
        "(EthLib.Serialization.Rlp.RlpError.leadingZeroInScalar)))"
    ),
    ("test_bal_invalid_ordering", "balance_changes_out_of_order"): (
        _INVALID + "balanceChangesNotAscending\n  #v[246, 195, 169, 237, 193, 175, 160, 173, "
        "91, 114, 14, 77, 66, 225, 67, 124, 67, 211, 179, 255]"
    ),
    ("test_bal_invalid_ordering", "code_changes_out_of_order"): (
        _INVALID + "codeChangesNotAscending\n  #v[192, 246, 220, 158, 88, 54, 245, 76, 170, "
        "219, 245, 156, 198, 147, 70, 197, 8, 225, 153, 43]"
    ),
    ("test_bal_invalid_ordering", "nonce_changes_out_of_order"): (
        _INVALID + "nonceChangesNotAscending\n  #v[246, 195, 169, 237, 193, 175, 160, 173, "
        "91, 114, 14, 77, 66, 225, 67, 124, 67, 211, 179, 255]"
    ),
    ("test_bal_invalid_ordering", "slot_changes_out_of_order"): (
        _INVALID + "storageChangesNotAscending\n  #v[91, 70, 29, 63, 129, 119, 180, 238, 152, "
        "26, 224, 164, 55, 194, 242, 36, 191, 123, 64, 199]\n  "
        "0x0000000000000000000000000000000000000000000000000000000000000001#256"
    ),
    ("test_bal_invalid_ordering", "storage_reads_out_of_order"): (
        _INVALID + "readsNotAscending\n  #v[91, 70, 29, 63, 129, 119, 180, 238, 152, 26, 224, "
        "164, 55, 194, 242, 36, 191, 123, 64, 199]"
    ),
    ("test_bal_invalid_ordering", "storage_slots_out_of_order"): (
        _INVALID + "slotsNotAscending\n  #v[91, 70, 29, 63, 129, 119, 180, 238, 152, 26, 224, "
        "164, 55, 194, 242, 36, 191, 123, 64, 199]"
    ),
    ("test_bal_invalid_tx_order", ""): (
        _INVALID + "balanceChangesNotAscending\n  #v[42, 220, 37, 102, 80, 24, 170, 31, 224, "
        "230, 188, 102, 109, 172, 143, 194, 105, 127, 249, 186]"
    ),
}


@pytest.mark.parametrize("case", VALID, ids=_id)
def test_valid_list(case) -> None:
    bal = bytes.fromhex(case["bal"])
    # The hash is the one that the header of the block holds.
    assert blocks.block_access_list_hash(bal).hex() == case["hash"]
    blocks.check_block_access_list(bal, case["gasLimit"])


@pytest.mark.parametrize("case", [c for c in INVALID if _function(c) in FORM], ids=_id)
def test_form_rejected(case) -> None:
    with raises(blocks.BlockError, _message(case)) as error:
        blocks.check_block_access_list(bytes.fromhex(case["bal"]), case["gasLimit"])
    assert error.value.code in FORM_CODES


@pytest.mark.parametrize("case", [c for c in INVALID if _function(c) in ENCODING], ids=_id)
def test_encoding_rejected(case) -> None:
    # The decoder rejects the bytes, so no hash exists.
    with raises(blocks.BlockError, _message(case)):
        blocks.block_access_list_hash(bytes.fromhex(case["bal"]))


@pytest.mark.parametrize(
    "case",
    [c for c in INVALID if c["error"].endswith("BLOCK_ACCESS_LIST_GAS_LIMIT_EXCEEDED")],
    ids=_id,
)
def test_too_many_items(case) -> None:
    with raises(blocks.BlockError, _message(case)) as error:
        blocks.check_block_access_list(bytes.fromhex(case["bal"]), case["gasLimit"])
    assert error.value.code == TOO_MANY_ITEMS


# The tests whose payloads keep the form of a list but disagree with the block.
# They record an access that the block does not make, or miss one that it makes.
# Or they carry a wrong value.
# So only executing the block can reject them.
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


# The payloads of those tests that also break the form.
# An extra or reordered entry lands out of order, or reads and writes one slot.
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
    # Every other invalid case belongs to a test that needs block execution.
    # So a new kind of case that no test reads fails here.
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
        with raises(blocks.BlockError, _message(case)) as error:
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
    with raises(
        blocks.BlockError,
        "block access list invalid: EthLib.Execution.Blocks.BlockAccessList.Error.tooManyItems 1 0",
    ) as error:
        blocks.check_block_access_list(bal, 1999)
    assert error.value.code == TOO_MANY_ITEMS
