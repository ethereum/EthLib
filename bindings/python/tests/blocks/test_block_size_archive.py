"""The block size limit of EIP-7934 against the Osaka blockchain tests of the release archive."""

import json

import pytest

from ethlib.execution import blocks

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

_DIRECTORY = "fixtures/blockchain_tests/for_osaka/osaka/eip7934_block_rlp_limit/max_block_rlp_size"
SOURCES = [
    f"{_DIRECTORY}/{name}.json"
    for name in [
        "block_at_rlp_limit_with_logs",
        "block_at_rlp_limit_with_withdrawals",
        "block_at_rlp_size_limit_boundary",
        "block_rlp_size_at_limit_with_all_typed_transactions",
    ]
]

pytestmark = pytest.mark.archive(ARCHIVE, *SOURCES)

TOO_LARGE = "BlockException.RLP_BLOCK_LIMIT_EXCEEDED"


@pytest.mark.parametrize("source", SOURCES, ids=lambda s: s.rsplit("/", 1)[-1])
def test_block_size(archive, source) -> None:
    checked = {"valid": 0, "too large": 0}
    for fixture in json.loads((archive / source).read_text()).values():
        if fixture["network"] != "Osaka":
            continue
        for block in fixture["blocks"]:
            data = bytes.fromhex(block["rlp"].removeprefix("0x"))
            exception = block.get("expectException", "")
            if not exception:
                # A valid block passes the size check.
                blocks.validate_size("fusaka", data)
                checked["valid"] += 1
            elif exception.split("|") == [TOO_LARGE]:
                with pytest.raises(blocks.BlockError) as error:
                    blocks.validate_size("fusaka", data)
                assert error.value.code == 214
                checked["too large"] += 1
    assert checked["valid"] > 0
    # The release has one block above the limit, in the boundary file.
    if "boundary" in source:
        assert checked["too large"] > 0
