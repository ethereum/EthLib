"""Header checks against consecutive fixture blocks and hand-made mutations."""

import json
import os
from itertools import pairwise
from pathlib import Path

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
    for _, blocks_of_test in sorted(by_test.items()):
        if "genesis" in blocks_of_test and 0 in blocks_of_test:
            genesis, child = blocks_of_test["genesis"], blocks_of_test[0]
            if genesis["network"] in AFTER_MERGE:
                yield genesis, child


PAIRS = list(_pairs())


def _headers(pair):
    genesis, child = pair
    return (
        _first_item(bytes.fromhex(genesis["rlp"])),
        _first_item(bytes.fromhex(child["rlp"])),
        FORK_OF_NETWORK[genesis["network"]],
    )


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
@pytest.mark.parametrize(
    "index,value,code",
    [
        (11, b"", 206),  # timestamp 0, not after the parent
        (12, b"\x00" * 33, 208),  # 33 bytes of extra data
        (10, (2**63).to_bytes(8, "big"), 203),  # gas used above the gas limit
        (9, (2**40).to_bytes(6, "big"), 204),  # a gas limit far above the parent's
    ],
)
def test_mutated_header_is_invalid(index: int, value: bytes, code: int) -> None:
    parent, header, fork = _headers(PAIRS[0])
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header(fork, fork, parent, _mutated(header, index, value))
    assert error.value.code == code


_INVALID = json.loads(
    (
        Path(__file__).resolve().parents[4]
        / "tests"
        / "execution"
        / "blocks"
        / "invalid_headers.json"
    ).read_text()
)


@pytest.mark.parametrize(
    "case",
    _INVALID,
    ids=[f"{c['network']}-{c['test'].split('::')[-1][:70]}-{c['block']}" for c in _INVALID],
)
def test_fixture_invalid_header(case) -> None:
    fork = FORK_OF_NETWORK[case["network"]]
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header(
            fork, fork, bytes.fromhex(case["parent"]), bytes.fromhex(case["header"])
        )
    # The first failed check is the one that the fixture names.
    assert error.value.code in case["codes"]


def test_invalid_headers_cover_each_check() -> None:
    assert {code for c in _INVALID for code in c["codes"]} == {202, 204, 205}


# EIP-7934: from Fusaka, the RLP form of a block has at most 10 MiB minus 2 MiB.
MAX_RLP_BLOCK_SIZE = 10_485_760 - 2_097_152


def _block_of_size(size: int) -> bytes:
    """A Fusaka fixture block whose one transaction is a byte string sized to give `size` bytes."""
    case = next(c for c in CASES if c["network"] == "Osaka")
    fields = rlp.decode(bytes.fromhex(case["rlp"]))
    filler = size
    while True:
        fields[1] = [b"\x02" + b"\x00" * filler]
        block = rlp.encode(fields)
        if len(block) == size:
            return block
        filler -= len(block) - size


def test_block_at_size_limit_is_valid() -> None:
    blocks.validate_size("fusaka", _block_of_size(MAX_RLP_BLOCK_SIZE))


def test_block_above_size_limit_is_invalid() -> None:
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_size("fusaka", _block_of_size(MAX_RLP_BLOCK_SIZE + 1))
    assert error.value.code == 214


def test_size_limit_starts_at_fusaka() -> None:
    # The same oversized block passes at Pectra, which has no size limit.
    block = _block_of_size(MAX_RLP_BLOCK_SIZE + 1)
    case = next(c for c in CASES if c["network"] == "Prague")
    fields = rlp.decode(bytes.fromhex(case["rlp"]))
    fields[1] = rlp.decode(block)[1]
    blocks.validate_size("pectra", rlp.encode(fields))


def test_paris_header_fails_the_difficulty_before_paris() -> None:
    # A Paris header has the 16 fields of London, so it decodes at London too.
    # Its difficulty is 0, below the minimum of 131,072 that London asks.
    paris = next(p for p in PAIRS if p[0]["network"] == "Paris")
    parent, header, _ = _headers(paris)
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header("london", "london", parent, header)
    assert error.value.code == 215


def _chain_pairs():
    """Each pair of consecutive fixture blocks of one test, at every fork."""
    by_test = {}
    for case in CASES:
        by_test.setdefault((case["source"], case["test"]), []).append(case)
    for cases in by_test.values():
        order = {"genesis": -1}
        cases = sorted(cases, key=lambda c: order.get(c["block"], c["block"]))
        for parent, child in pairwise(cases):
            if parent["block"] == "genesis" or child["block"] == parent["block"] + 1:
                yield parent, child


CHAIN_PAIRS = list(_chain_pairs())


@pytest.mark.parametrize(
    "pair",
    CHAIN_PAIRS,
    ids=[f"{p[0]['network']}-{p[0]['test'][-40:]}-{p[1]['block']}" for p in CHAIN_PAIRS],
)
def test_fixture_chain_passes_the_header_checks(pair) -> None:
    # The fixtures run without proof of work, so every check but the seal applies.
    parent, header, fork = _headers(pair)
    blocks.check_header(fork, fork, parent, header)


def test_chain_pairs_cover_every_fork() -> None:
    assert {p[0]["network"] for p in CHAIN_PAIRS} == set(FORK_OF_NETWORK)


def test_wrong_difficulty_before_paris_is_rejected() -> None:
    # A Frontier block with its difficulty raised by one fails the difficulty rule.
    pair = next(p for p in CHAIN_PAIRS if p[0]["network"] == "Frontier")
    parent, header, fork = _headers(pair)
    difficulty = int.from_bytes(rlp.decode(header)[7], "big") + 1
    with pytest.raises(blocks.BlockError) as error:
        blocks.check_header(
            fork, fork, parent, _mutated(header, 7, difficulty.to_bytes(8, "big").lstrip(b"\x00"))
        )
    assert error.value.code == 215


@pytest.mark.skipif(
    os.environ.get("ETHLIB_SLOW_VECTORS") != "1", reason="the Ethash cache of epoch 0, run weekly"
)
def test_unsealed_header_fails_the_proof_of_work() -> None:
    # The fixtures carry no proof of work, so the full check rejects them before Paris.
    pair = next(p for p in CHAIN_PAIRS if p[0]["network"] == "Frontier")
    parent, header, fork = _headers(pair)
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header(fork, fork, parent, header)
    assert error.value.code == 216
