"""The runners of the legacy blockchain tests of ethereum/legacytests, from Frontier to London."""

import json
from dataclasses import dataclass
from functools import cache
from pathlib import Path

import pytest

from ethlib.errors import BlockError
from ethlib.execution import blocks
from ethlib.execution.pow import validate_ommers
from ethlib.serialization import rlp

from .catalogue import LEGACY_FORKS, Case

# The block from which a transition network runs its second fork.
TRANSITION_BLOCK = 5

# The most recent blocks that the ommer check reads: the parent of a block and six before it.
RECENT_BLOCKS = 7

# The name of each header error code, as the message of the error spells it.
HEADER_ERRORS = {
    201: "genesisNumber",
    203: "gasUsedAboveLimit",
    204: "invalidGasLimit",
    205: "wrongBaseFee",
    206: "timestampNotAfterParent",
    207: "wrongNumber",
    208: "extraDataTooLong",
    215: "wrongDifficulty",
    216: "proofOfWork",
}

# The code of an ommer that is not a valid header, and of an ommer whose number is out of range.
INVALID_OMMER_HEADER = 234
OMMER_NUMBER_OUT_OF_RANGE = 232

# The header errors that each exception names, in the header of the block or of one of its ommers.
# A zero gas limit is also below the gas used, which the header check tests first.
# A block numbered 0 has the number of a genesis block, which no parent precedes.
# From London, a difficulty of 0 is that of a proof-of-stake block, which the check refuses.
HEADER_CODES = {
    "InvalidDifficulty": {215},
    "InvalidGasLimit": {204},
    "InvalidGasLimit2": {203, 204},
    "BlockException.INVALID_GASLIMIT": {204},
    "InvalidNumber": {201, 207},
    "InvalidTimestamp": {206},
    "InvalidTimestampOlderParent": {206},
    "ExtraDataTooBig": {208},
    "TooMuchGasUsed": {203},
    "1559BlockImportImpossible_BaseFeeWrong": {205},
    "3675PoSBlockRejected": {215},
    "InvalidBlockNonce": {216},
}

# The exceptions of a block whose parent is in no test chain.
UNKNOWN_PARENT = {"UnknownParent", "UnknownParent2", "BlockException.UNKNOWN_PARENT"}

# The exceptions that a header check cannot see.
# They concern the body, the execution, the ommer rules, or the DAO Fork rule of a chain
# configuration, so a block with one of them has a valid header.
NOT_IN_HEADER = {
    "InvalidStateRoot", "InvalidReceiptsStateRoot", "InvalidLogBloom", "InvalidTransactionsRoot",
    "InvalidGasUsed", "BlockGasLimitReached", "BlockException.INVALID_GAS_USED",
    "InvalidUnclesHash", "InvalidUncleParentHash", "TooManyUncles", "UncleInChain",
    "UncleIsAncestor", "UncleIsBrother", "UncleParentIsNotAncestor", "UncleTooOld",
    "BlockException.UNCLE_PARENT_INCORRECT", "BlockException.EXTRA_DATA_INVALID_DAO",
    # An ommer in the header form of the other side of the London transition.
    "BlockException.IMPORT_IMPOSSIBLE_LONDON_WRONG_PARENT",
    "BlockException.IMPORT_IMPOSSIBLE_LEGACY_WRONG_PARENT",
}


@dataclass(frozen=True)
class Block:
    """A block of a test chain: its fork, its header hash, and the RLP of its header and itself."""

    fork: str
    hash: str
    header: bytes
    block: bytes

    @property
    def parent_hash(self) -> str:
        """The parent hash, in the hexadecimal form of the fixtures."""
        return "0x" + rlp.decode(self.header)[0].hex()


@cache
def _fixtures(path: Path) -> dict:
    return json.loads(path.read_text())


def fixture(root: Path, case: Case) -> dict:
    """The blockchain test of a case."""
    # The identifier is the path, two colons and the name, which can hold colons itself.
    return _fixtures(root / case.path)[case.id.removeprefix(f"{case.path}::")]


def fork_at(network: str, number: int) -> str:
    """The fork of a network at a block number."""
    forks = LEGACY_FORKS[network]
    return forks[-1] if number >= TRANSITION_BLOCK else forks[0]


def header_fields(fork: str) -> int:
    """The number of fields of a header at a fork from Frontier to London."""
    return 16 if fork == "london" else 15


def exception(network: str, entry: dict) -> str | None:
    """The exception that a block expects at the network, or `None` for a valid block."""
    for key in (f"expectException{network}", "expectExceptionALL", "expectException"):
        if key in entry:
            return entry[key]
    return None


def rejects_transaction(name: str) -> bool:
    """Whether an exception rejects a transaction of the block, which the header never shows."""
    return name.startswith(("TR_", "TransactionException."))


def sealed(test: dict) -> bool:
    """Whether the blocks of a test carry a proof of work."""
    return test.get("sealEngine") == "Ethash"


def recent(chain: dict[str, Block], parent: Block) -> list[bytes]:
    """The blocks that end with `parent`, at most seven, the oldest first."""
    blocks_ = [parent]
    while len(blocks_) < RECENT_BLOCKS and blocks_[-1].parent_hash in chain:
        blocks_.append(chain[blocks_[-1].parent_hash])
    return [b.block for b in reversed(blocks_)]


def _header_error(network: str, test: dict, chain: dict, parent: Block, block: Block,
                  expected: str) -> None:
    """Check that the header of the block or of one of its ommers fails as the exception says."""
    codes = HEADER_CODES[expected]
    check = blocks.validate_header if sealed(test) else blocks.check_header
    try:
        check(parent.fork, block.fork, parent.header, block.header)
    except BlockError as error:
        assert error.code in codes, (expected, str(error))
        return
    # The header of the block is valid, so the exception names an ommer.
    with pytest.raises(BlockError) as error:
        validate_ommers(block.fork, recent(chain, parent), block.block, sealed(test))
    message = str(error.value)
    if error.value.code == OMMER_NUMBER_OUT_OF_RANGE:
        # An ommer numbered 0 or not below the block fails before its header is read.
        assert codes & {201, 207}, (expected, message)
        return
    assert error.value.code == INVALID_OMMER_HEADER, (expected, message)
    if any(f"BlockError.{HEADER_ERRORS[code]}" in message for code in codes):
        return
    # The ommer check takes the parent of an ommer to be the recent block one number below it.
    # An ommer with a wrong number then fails against a block that is not its parent, at the
    # first check that this block breaks.
    assert codes & {207}, message
    headers = {_number(b[0]): b[0] for b in map(rlp.decode, recent(chain, parent))}
    assert any(_number(ommer) - 1 in headers
               and ommer[0] != blocks.header_hash(block.fork, rlp.encode(headers[_number(ommer) - 1]))
               for ommer in rlp.decode(block.block)[2]), message


def _number(header: list) -> int:
    return int.from_bytes(header[8], "big")


def run_headers(root: Path, case: Case) -> None:
    """Check each header against its parent, with the proof of work when the test seals it."""
    test = fixture(root, case)
    network = test["network"]
    check = blocks.validate_header if sealed(test) else blocks.check_header
    chain: dict[str, Block] = {}
    checked = 0
    entries = [(test["genesisRLP"], None)] + [(e["rlp"], e) for e in test["blocks"]]
    for data, entry in entries:
        data = bytes.fromhex(data.removeprefix("0x"))
        expected = exception(network, entry) if entry else None
        fields = rlp.decode(data)[0]
        fork = fork_at(network, int.from_bytes(fields[8], "big"))
        header = rlp.encode(fields)
        if len(fields) != header_fields(fork):
            # A header in the form of another fork decodes at no fork that its number runs.
            assert expected is not None
            with pytest.raises(BlockError, match="wrongFieldCount"):
                blocks.header_hash(fork, header)
            checked += 1
            continue
        block = Block(fork, "0x" + blocks.header_hash(fork, header).hex(), header, data)
        if entry is None:
            assert block.hash == test["genesisBlockHeader"]["hash"]
            chain[block.hash] = block
            continue
        parent = chain.get(block.parent_hash)
        if expected in UNKNOWN_PARENT:
            assert parent is None, block.hash
        elif expected is None or expected in NOT_IN_HEADER or rejects_transaction(expected):
            assert parent is not None, block.hash
            check(parent.fork, block.fork, parent.header, block.header)
            if expected is None:
                assert block.hash == entry["blockHeader"]["hash"]
                chain[block.hash] = block
        else:
            assert expected in HEADER_CODES, f"no header code for {expected}"
            assert parent is not None, block.hash
            _header_error(network, test, chain, parent, block, expected)
        checked += 1
    assert checked > 0
