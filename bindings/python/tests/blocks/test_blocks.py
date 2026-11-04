"""Headers and blocks against the blockchain tests of execution-specs.

The cases are in `tests/execution/blocks/blockchain_tests.json`, whose README gives their origin.
Each case is one valid block of one fork, with the hash of its header.

For each case, the decoder at the fork of the case must accept the block and encode it back
byte for byte, and the header must hash to the hash that the fixture gives.
"""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks

_REPO = Path(__file__).resolve().parents[4]
_CASES_FILE = _REPO / "tests" / "execution" / "blocks" / "blockchain_tests.json"
CASES = json.loads(_CASES_FILE.read_text())

# The network of a fixture, and the case of the Lean fork type that it names.
FORK_OF_NETWORK = {
    "Frontier": "frontier",
    "Homestead": "homestead",
    "TangerineWhistle": "tangerineWhistle",
    "SpuriousDragon": "spuriousDragon",
    "Byzantium": "byzantium",
    "ConstantinopleFix": "petersburg",
    "Istanbul": "istanbul",
    "Berlin": "berlin",
    "London": "london",
    "Paris": "paris",
    "Shanghai": "shapella",
    "Cancun": "dencun",
    "Prague": "pectra",
    "Osaka": "fusaka",
    "Amsterdam": "glamsterdam",
}

# The networks before London, whose headers have the 15 fields of Frontier.
BEFORE_LONDON = {"Frontier", "Homestead", "TangerineWhistle", "SpuriousDragon", "Byzantium",
                 "ConstantinopleFix", "Istanbul", "Berlin"}


def _first_item(data: bytes) -> bytes:
    """The encoding of the first item in the payload of the RLP list `data`.

    A block and its header are long lists, so both prefixes are in the long form.
    """
    assert data[0] >= 0xF8
    start = 1 + data[0] - 0xF7
    head = data[start]
    assert head >= 0xF8
    length_bytes = head - 0xF7
    length = int.from_bytes(data[start + 1:start + 1 + length_bytes], "big")
    return data[start:start + 1 + length_bytes + length]


def _case_id(case) -> str:
    return f"{case['network']}-{case['test'].split('::')[-1][:60]}-{case['block']}"


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_fixture_block(case) -> None:
    fork = FORK_OF_NETWORK[case["network"]]
    block = bytes.fromhex(case["rlp"])
    # The decoder accepts the block, and its encoding gives back the same bytes.
    assert blocks.reencode(fork, block) == block
    # The header hashes to the hash of the fixture.
    assert blocks.header_hash(fork, _first_item(block)) == bytes.fromhex(case["hash"])


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_header_rejected_at_other_fork(case) -> None:
    # A London header has one more field than a Frontier header, so each fork rejects the other.
    other = "london" if case["network"] in BEFORE_LONDON else "frontier"
    header = _first_item(bytes.fromhex(case["rlp"]))
    with pytest.raises(ValueError):
        blocks.header_hash(other, header)


def test_trailing_byte_rejected() -> None:
    case = CASES[0]
    block = bytes.fromhex(case["rlp"])
    with pytest.raises(ValueError):
        blocks.reencode(FORK_OF_NETWORK[case["network"]], block + b"\x00")


def test_unknown_fork_rejected() -> None:
    with pytest.raises(ValueError):
        blocks.reencode("prague", bytes.fromhex(CASES[0]["rlp"]))


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        blocks.reencode("frontier", "c0")  # type: ignore[arg-type]
