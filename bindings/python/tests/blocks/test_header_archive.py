"""The header checks from Frontier to Paris against every blockchain test of the release archive."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from raising import raises

from .expected_errors import expected_message
from .test_blocks import FORK_OF_NETWORK, _first_item

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

# The directories of the release that fill a network from Frontier to Paris.
DIRECTORIES = [
    "for_frontier",
    "for_homestead",
    "for_tangerinewhistle",
    "for_spuriousdragon",
    "for_byzantium",
    "for_constantinoplefix",
    "for_istanbul",
    "for_berlin",
    "for_london",
    "for_paris",
]
SOURCES = [f"fixtures/blockchain_tests/{d}" for d in DIRECTORIES]

# The exceptions of a block that a header check raises, with its code.
CODES = {
    "BlockException.INVALID_GASLIMIT": 204,
    "BlockException.INVALID_BASEFEE_PER_GAS": 205,
}

pytestmark = pytest.mark.archive(ARCHIVE, *SOURCES)


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


@pytest.mark.parametrize("directory", DIRECTORIES)
def test_headers_of_every_fixture(archive: Path, directory: str) -> None:
    checked = 0
    for path in sorted((archive / "fixtures" / "blockchain_tests" / directory).rglob("*.json")):
        for name, fixture in json.loads(path.read_text()).items():
            fork = FORK_OF_NETWORK[fixture["network"]]
            genesis = _first_item(_hex(fixture["genesisRLP"]))
            headers = {fixture["genesisBlockHeader"]["hash"]: genesis}
            for block in fixture["blocks"]:
                header = _first_item(_hex(block["rlp"]))
                exception = block.get("expectException")
                if not exception:
                    # A valid block passes every check but the proof of work, which the
                    # fixtures do not carry.
                    blocks.check_header(
                        fork, fork, headers[block["blockHeader"]["parentHash"]], header
                    )
                    headers[block["blockHeader"]["hash"]] = header
                    checked += 1
                    continue
                named = [e for e in exception.split("|") if e in CODES]
                parent = headers.get("0x" + header[4:36].hex())
                if not named or parent is None:
                    continue
                # Each such block names one exception, and the header check fails on it.
                assert len(named) == 1, f"{path.name}::{name}"
                message = expected_message(named[0], parent, header, None, False)
                with raises(blocks.BlockError, message) as error:
                    blocks.check_header(fork, fork, parent, header)
                assert error.value.code == CODES[named[0]], f"{path.name}::{name}"
    # Every directory has valid blocks to check.
    assert checked > 0
