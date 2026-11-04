"""Header checks against consecutive fixture blocks and hand-made mutations."""

import pytest

from ethlib.execution import blocks
from ethlib.serialization import rlp

from .test_blocks import CASES, FORK_OF_NETWORK, _first_item

# The networks from Paris on, where the header checks apply.
AFTER_MERGE = {"Paris", "Shanghai", "Cancun", "Prague", "Osaka", "Amsterdam"}


def _pairs():
    """Each fixture block 0 after Paris, with the genesis block of its test."""
    by_test = {}
    for case in CASES:
        by_test.setdefault((case["source"], case["test"]), {})[case["block"]] = case
    for (_, test), blocks_of_test in sorted(by_test.items()):
        if "genesis" in blocks_of_test and 0 in blocks_of_test:
            genesis, child = blocks_of_test["genesis"], blocks_of_test[0]
            if genesis["network"] in AFTER_MERGE:
                yield genesis, child


PAIRS = list(_pairs())


def _headers(pair):
    genesis, child = pair
    return (_first_item(bytes.fromhex(genesis["rlp"])), _first_item(bytes.fromhex(child["rlp"])),
            FORK_OF_NETWORK[genesis["network"]])


PAIR_IDS = [f"{p[0]['network']}-{p[0]['test'][-50:]}" for p in PAIRS]


@pytest.mark.parametrize("pair", PAIRS, ids=PAIR_IDS)
def test_fixture_header_is_valid(pair) -> None:
    parent, header, fork = _headers(pair)
    blocks.validate_header(fork, fork, parent, header)


def _mutated(header: bytes, index: int, value: bytes) -> bytes:
    fields = rlp.decode(header)
    fields[index] = value
    return rlp.encode(fields)


# Field positions in the header list: gas limit 9, gas used 10, timestamp 11, extra data 12.
@pytest.mark.parametrize("index,value,code", [
    (11, b"", 206),                             # timestamp 0, not after the parent
    (12, b"\x00" * 33, 208),                    # 33 bytes of extra data
    (10, (2 ** 63).to_bytes(8, "big"), 203),    # gas used above the gas limit
    (9, (2 ** 40).to_bytes(6, "big"), 204),     # a gas limit far above the parent's
])
def test_mutated_header_is_invalid(index: int, value: bytes, code: int) -> None:
    parent, header, fork = _headers(PAIRS[0])
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header(fork, fork, parent, _mutated(header, index, value))
    assert error.value.code == code


def test_header_before_paris_is_rejected() -> None:
    # A Paris header has the 16 fields of London, so it decodes at London too.
    paris = next(p for p in PAIRS if p[0]["network"] == "Paris")
    parent, header, _ = _headers(paris)
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header("london", "london", parent, header)
    assert error.value.code == 0
