"""The ommer checks, on ommers made from a Frontier chain of the blockchain tests.

No pinned test of the release holds an ommer, so each ommer here is a fixture header with one
field changed, which keeps it a valid header of a block that the chain left out.
"""

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.errors import BlockError
from ethlib.execution.pow import validate_ommers
from ethlib.serialization import rlp
from raising import raises

from .test_blocks import CASES

# The genesis block and the three blocks of one Frontier chain, in order.
_CHAIN = sorted(
    (c for c in CASES if c["network"] == "Frontier"),
    key=lambda c: -1 if c["block"] == "genesis" else c["block"],
)
BLOCKS = [rlp.decode(bytes.fromhex(c["rlp"])) for c in _CHAIN]

FORK = "frontier"


def _with_coinbase(header: list, byte: int) -> list:
    """The header with another beneficiary, so another hash, and still a valid header."""
    header = list(header)
    header[2] = bytes([byte]) * 20
    return header


def _block(ommers: list, ommers_hash: bytes | None = None) -> bytes:
    """The last block of the chain, holding `ommers`, with their hash in its header."""
    header, transactions, _ = BLOCKS[3]
    header = list(header)
    header[1] = keccak256(rlp.encode(ommers)) if ommers_hash is None else ommers_hash
    return rlp.encode([header, transactions, ommers])


# The recent chain of the last block: the genesis block and the two blocks after it.
RECENT = [rlp.encode(b) for b in BLOCKS[:3]]

# An ommer: block 2 of the chain, at the same height and with the same parent, mined by another.
OMMER = _with_coinbase(BLOCKS[2][0], 0x11)


def _code(recent: list[bytes], block: bytes, error: str) -> int:
    with raises(
        BlockError, f"ommers invalid: EthLib.Execution.Blocks.OmmerError.{error}"
    ) as caught:
        validate_ommers(FORK, recent, block, check_seal=False)
    return caught.value.code


def test_chain_is_frontier_genesis_and_three_blocks() -> None:
    assert [int.from_bytes(b[0][8], "big") for b in BLOCKS] == [0, 1, 2, 3]


def test_no_ommer_passes() -> None:
    assert validate_ommers(FORK, RECENT, rlp.encode(BLOCKS[3]), check_seal=False)


def test_one_ommer_passes() -> None:
    assert validate_ommers(FORK, RECENT, _block([OMMER]), check_seal=False)


def test_two_ommers_pass() -> None:
    assert validate_ommers(
        FORK, RECENT, _block([OMMER, _with_coinbase(BLOCKS[2][0], 0x22)]), check_seal=False
    )


def test_wrong_ommers_hash() -> None:
    assert _code(RECENT, _block([OMMER], ommers_hash=BLOCKS[3][0][1]), "wrongOmmersHash") == 231


def test_ommer_as_old_as_the_block() -> None:
    # An ommer at the block's own height is out of range.
    assert _code(RECENT, _block([_with_coinbase(BLOCKS[3][0], 0x11)]), "numberOutOfRange") == 232


def test_ommer_without_its_parent_in_the_recent_chain() -> None:
    # The recent chain skips block 1, the parent of the ommer.
    assert _code([RECENT[0], RECENT[2]], _block([OMMER]), "parentMissing") == 233


def test_ommer_that_is_not_a_valid_header() -> None:
    # A difficulty raised by one breaks the difficulty rule.
    ommer = list(OMMER)
    ommer[7] = (int.from_bytes(ommer[7], "big") + 1).to_bytes(3, "big")
    error = "invalidHeader (EthLib.Execution.Blocks.BlockError.wrongDifficulty 131200 131201)"
    assert _code(RECENT, _block([ommer]), error) == 234


def test_three_ommers() -> None:
    ommers = [_with_coinbase(BLOCKS[2][0], b) for b in (0x11, 0x22, 0x33)]
    assert _code(RECENT, _block(ommers), "tooManyOmmers") == 235


def test_one_ommer_twice() -> None:
    assert _code(RECENT, _block([OMMER, OMMER]), "duplicateOmmer") == 236


def test_ommer_that_is_a_block_of_the_chain() -> None:
    assert _code(RECENT, _block([BLOCKS[2][0]]), "ommerInChain") == 237


def test_ommer_already_included_by_a_recent_block() -> None:
    parent = list(BLOCKS[2])
    parent[2] = [OMMER]
    recent = RECENT[:2] + [rlp.encode(parent)]
    assert _code(recent, _block([OMMER]), "ommerAlreadyIncluded") == 238


def test_forks_given_with_their_first_blocks() -> None:
    # A chain of one fork from block 0 is the fork given by its name.
    assert validate_ommers([(FORK, 0)], RECENT, _block([OMMER]), check_seal=False)


def _code_with(forks: list[tuple[str, int]], message: str) -> int:
    with raises(BlockError, message) as error:
        validate_ommers(forks, RECENT, _block([OMMER]), check_seal=False)
    return error.value.code


@pytest.mark.parametrize(
    "forks, message",
    [
        ([(FORK, 1)], "the first fork does not start at block 0"),
        ([("homestead", 0), (FORK, 5)], "the forks are not in the order of the timeline"),
        ([(FORK, 0), ("hegota", 5)], "fork hegota not yet specified"),
    ],
)
def test_forks_that_no_chain_runs(forks: list[tuple[str, int]], message: str) -> None:
    # The first fork starts after block 0, the forks are out of order, or a fork is not specified.
    assert _code_with(forks, message) == 0
