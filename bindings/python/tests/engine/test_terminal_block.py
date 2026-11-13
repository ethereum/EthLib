"""The terminal block check of engine_newPayloadV1 on a parent of proof of work."""

# Rules of the check: step 2 of payload validation, and the definitions of EIP-3675.
# A block is terminal when its total difficulty reaches the terminal total difficulty.
# The total difficulty of its parent, its own total minus its difficulty, must not reach it.
#
# ethereum/execution-apis, src/engine/paris.md, commit 3284ee80c3da3e516c53782dde75157cccf1ebdc.
# ethereum/EIPs, EIPS/eip-3675.md, commit 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445.
#
# No official vector has a parent before Paris: the engine fixtures all start at Paris.

import pytest

from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from ethlib.serialization import rlp
from raising import raises

from .cases import BLOCK_FORKS, DEPOSIT_CONTRACT_ADDRESS

# London from block 0, so the genesis block is of proof of work, and Paris from block 1.
CONFIG = {
    "chainId": 1,
    "depositContractAddress": DEPOSIT_CONTRACT_ADDRESS,
    "activations": [[fork, "block", 0] for fork in BLOCK_FORKS[:-1]] + [["paris", "block", 1]],
}

# Paris from block 0, so the genesis block is already of proof of stake.
PARIS_CONFIG = {
    "chainId": 1,
    "depositContractAddress": DEPOSIT_CONTRACT_ADDRESS,
    "activations": [[fork, "block", 0] for fork in BLOCK_FORKS],
}

# A chain without accounts.
STATE = rlp.encode([])

# The root of an empty trie, and the hash of an empty list of ommers.
EMPTY_ROOT = keccak256(rlp.encode(b""))
EMPTY_OMMERS = keccak256(rlp.encode([]))

# The difficulty of the London genesis block.
DIFFICULTY = 15

# The terminal total difficulty of mainnet, from the configuration section of EIP-3675.
MAINNET_TERMINAL_TOTAL_DIFFICULTY = 58750000000000000000000

GAS_LIMIT = 30_000_000
PARENT_BASE_FEE = 1_000_000_000
# EIP-1559 lowers the base fee by an eighth after a block that uses no gas.
BASE_FEE = PARENT_BASE_FEE - PARENT_BASE_FEE // 8

ZERO_HASH = "0x" + bytes(32).hex()

# The message of the reason, after its code.
NOT_TERMINAL = "407: the parent is a block of proof of work that is not terminal"


def _number(n: int) -> bytes:
    """The bytes of a number for RLP: big-endian, without leading zeros."""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _header(parent_hash: bytes, difficulty: int, number: int, base_fee: int) -> bytes:
    """The RLP form of a London or Paris header with no transaction and no account."""
    return rlp.encode(
        [
            parent_hash,
            EMPTY_OMMERS,
            bytes(20),
            EMPTY_ROOT,
            EMPTY_ROOT,
            EMPTY_ROOT,
            bytes(256),
            _number(difficulty),
            _number(number),
            _number(GAS_LIMIT),
            b"",
            _number(number),
            b"",
            bytes(32),
            bytes(8),
            _number(base_fee),
        ]
    )


# A London genesis block with a difficulty, and a Paris one without.
GENESIS = _header(bytes(32), DIFFICULTY, 0, PARENT_BASE_FEE)
PARIS_GENESIS = _header(bytes(32), 0, 0, PARENT_BASE_FEE)


def _payload(parent_hash: bytes) -> dict:
    """Block 1 on a parent, with no transaction, as a payload whose hash is that of its header."""
    return {
        "parentHash": "0x" + parent_hash.hex(),
        "feeRecipient": "0x" + bytes(20).hex(),
        "stateRoot": "0x" + EMPTY_ROOT.hex(),
        "receiptsRoot": "0x" + EMPTY_ROOT.hex(),
        "logsBloom": "0x" + bytes(256).hex(),
        "prevRandao": ZERO_HASH,
        "blockNumber": "0x1",
        "gasLimit": hex(GAS_LIMIT),
        "gasUsed": "0x0",
        "timestamp": "0x1",
        "extraData": "0x",
        "baseFeePerGas": hex(BASE_FEE),
        "blockHash": "0x" + keccak256(_header(parent_hash, 0, 1, BASE_FEE)).hex(),
        "transactions": [],
    }


def _new_payload(
    payload: dict, *, terminal_total_difficulty: int, total_difficulty: int, paris: bool = False
) -> dict:
    """The status of a payload on the genesis block, whose total difficulty is given."""
    status, _, _ = engine.new_payload_on_chain(
        PARIS_CONFIG if paris else CONFIG,
        STATE,
        [("paris", PARIS_GENESIS, [])] if paris else [("london", GENESIS, [])],
        "engine_newPayloadV1",
        [payload],
        terminal_total_difficulty=terminal_total_difficulty,
        total_difficulty=total_difficulty,
    )
    return status


def _valid(payload: dict) -> dict:
    """The status of a valid payload."""
    return {"status": "VALID", "latestValidHash": payload["blockHash"], "validationError": None}


INVALID = {"status": "INVALID", "latestValidHash": ZERO_HASH, "validationError": NOT_TERMINAL}

# With a difficulty of 15, the genesis block is terminal exactly for totals from T to T + 14.
M = MAINNET_TERMINAL_TOTAL_DIFFICULTY
CASES = [
    # A terminal total difficulty of 100: below it, at it, inside, at the last value, past it.
    (100, 99, False),
    (100, 100, True),
    (100, 105, True),
    (100, 114, True),
    (100, 115, False),
    (100, 120, False),
    # The terminal total difficulty of mainnet, far above 64 bits.
    (M, M - 1, False),
    (M, M, True),
    (M, M + 15, False),
    # The largest terminal total difficulty that fits 256 bits.
    (2**256 - 1, 2**256 - 1, True),
    (2**256 - 1, 2**256 - 1 + 14, True),
    (2**256 - 1, 2**256 - 1 + 15, False),
    # A total below the difficulty of the block, which no real chain has, fails the check.
    (5, DIFFICULTY - 1, False),
]


@pytest.mark.parametrize("terminal_total_difficulty, total_difficulty, terminal", CASES)
def test_proof_of_work_parent(
    terminal_total_difficulty: int, total_difficulty: int, terminal: bool
) -> None:
    """A terminal parent lets the payload run; another parent of proof of work makes it invalid."""
    payload = _payload(keccak256(GENESIS))
    status = _new_payload(
        payload,
        terminal_total_difficulty=terminal_total_difficulty,
        total_difficulty=total_difficulty,
    )
    assert status == (_valid(payload) if terminal else INVALID)


@pytest.mark.parametrize("totals", [(100, 99), (2**256 - 1, 0), (1, 2**300)])
def test_paris_parent(totals: tuple[int, int]) -> None:
    """A parent from Paris on is not checked, whatever the totals."""
    terminal_total_difficulty, total_difficulty = totals
    payload = _payload(keccak256(PARIS_GENESIS))
    status = _new_payload(
        payload,
        terminal_total_difficulty=terminal_total_difficulty,
        total_difficulty=total_difficulty,
        paris=True,
    )
    assert status == _valid(payload)


def test_unknown_parent() -> None:
    """A payload whose parent is not the last block stays syncing, before the terminal check."""
    status = _new_payload(_payload(bytes(32)), terminal_total_difficulty=100, total_difficulty=99)
    assert status == {"status": "SYNCING", "latestValidHash": None, "validationError": None}


def test_terminal_total_difficulty_above_256_bits() -> None:
    """A terminal total difficulty of 2^256 does not fit the configuration."""
    with raises(
        engine.EngineError, f"config: a terminal total difficulty of {2**256}, not below 2^256"
    ) as error:
        _new_payload(
            _payload(keccak256(GENESIS)), terminal_total_difficulty=2**256, total_difficulty=0
        )
    assert error.value.code == 0
