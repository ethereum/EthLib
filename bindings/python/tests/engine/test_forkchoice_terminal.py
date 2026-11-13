"""The terminal block check and the zero hashes of engine_forkchoiceUpdatedV1 at the transition."""

# Rules: steps 3 and 9 of engine_forkchoiceUpdatedV1 and step 2 of payload validation.
# Also the note of ForkchoiceStateV1 on zero hashes, and the definitions of EIP-3675.
# A block is terminal when its total difficulty reaches the terminal total difficulty.
# The total difficulty of its parent must not reach it.
#
# ethereum/execution-apis, src/engine/paris.md, commit 3284ee80c3da3e516c53782dde75157cccf1ebdc.
# ethereum/EIPs, EIPS/eip-3675.md, commit 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445.
#
# No official vector has a block of proof of work: the engine fixtures all start at Paris.

import pytest

from ethlib import engine
from raising import raises

from .cases import BLOCK_FORKS, DEPOSIT_CONTRACT_ADDRESS, MAINNET_TERMINAL_TOTAL_DIFFICULTY

# London from block 0, so block 0 is of proof of work, and Paris from block 1.
CONFIG = {
    "chainId": 1,
    "depositContractAddress": DEPOSIT_CONTRACT_ADDRESS,
    "activations": [[fork, "block", 0] for fork in BLOCK_FORKS[:-1]] + [["paris", "block", 1]],
}

ZERO = "0x" + "00" * 32

INVALID_STATE = "engine error: EthLib.Engine.EngineError.invalidForkchoiceState"


def _hash(n: int) -> str:
    """The block hash of block `n`: `n` in 32 big-endian bytes."""
    return "0x" + n.to_bytes(32, "big").hex()


def _is_terminal(terminal_total_difficulty: int, total: int, parent_total: int) -> bool:
    """The definition of a terminal block of proof of work in EIP-3675."""
    return total >= terminal_total_difficulty and parent_total < terminal_total_difficulty


def _pow(block: int, parent: int, total: int, parent_total: int) -> dict:
    """A valid block of proof of work at number 0 and time 10, with its two totals."""
    # The check reads only the totals, so every block of proof of work shares one number.
    return {
        "blockHash": _hash(block),
        "parentHash": _hash(parent),
        "valid": True,
        "number": "0x0",
        "timestamp": "0xa",
        "totalDifficulty": hex(total),
        "parentTotalDifficulty": hex(parent_total),
    }


def _payload(block: int, parent: int, *, valid: bool = True) -> dict:
    """A payload at number 1 and time 20."""
    return {
        "blockHash": _hash(block),
        "parentHash": _hash(parent),
        "valid": valid,
        "number": "0x1",
        "timestamp": "0x14",
    }


def _update(
    tree: list,
    head: int,
    *,
    terminal_total_difficulty: int,
    safe: str = ZERO,
    finalized: str = ZERO,
    known_finalized: str | None = None,
    attributes: dict | None = None,
) -> dict:
    """The response of version 1 of the method, with a forkchoice state on a head."""
    state = {"headBlockHash": _hash(head), "safeBlockHash": safe, "finalizedBlockHash": finalized}
    return engine.forkchoice_updated(
        CONFIG,
        tree,
        "engine_forkchoiceUpdatedV1",
        [state, attributes],
        known_finalized,
        terminal_total_difficulty=terminal_total_difficulty,
    )


def _status(status: str, latest_valid_hash: str | None) -> dict:
    """A response with a status, a latest valid hash and no build."""
    return {
        "payloadStatus": {
            "status": status,
            "latestValidHash": latest_valid_hash,
            "validationError": None,
        },
        "payloadId": None,
    }


# The zero hash as latest valid hash, by step 9 for a head that fails the terminal check.
NOT_TERMINAL = _status("INVALID", ZERO)

# A terminal total difficulty, then the totals of block 1 and of its parent.
TOTALS = [
    # From a parent at 90, a total of 105 crosses 100, and one of 95 does not.
    (100, 105, 90),
    (100, 95, 90),
    # The total reaches the terminal total difficulty exactly, or the parent's does too.
    (100, 100, 99),
    (100, 110, 100),
    # The terminal total difficulty of mainnet, far above 64 bits.
    (
        MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        MAINNET_TERMINAL_TOTAL_DIFFICULTY - 1,
    ),
    (
        MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        MAINNET_TERMINAL_TOTAL_DIFFICULTY + 1,
        MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    ),
    (
        MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        MAINNET_TERMINAL_TOTAL_DIFFICULTY - 1,
        MAINNET_TERMINAL_TOTAL_DIFFICULTY - 2,
    ),
    # The largest terminal total difficulty of 256 bits, and totals at or above 2^256.
    (2**256 - 1, 2**256, 2**256 - 2),
    (2**256 - 1, 2**300, 2**256),
]


@pytest.mark.parametrize("terminal_total_difficulty, total, parent_total", TOTALS)
def test_proof_of_work_head(terminal_total_difficulty: int, total: int, parent_total: int) -> None:
    """A terminal head of proof of work becomes the head; another one is invalid, with zero."""
    tree = [_pow(1, 0, total, parent_total)]
    response = _update(tree, 1, terminal_total_difficulty=terminal_total_difficulty)
    if _is_terminal(terminal_total_difficulty, total, parent_total):
        assert response == _status("VALID", _hash(1))
    else:
        assert response == NOT_TERMINAL


@pytest.mark.parametrize("terminal_total_difficulty, total, parent_total", TOTALS)
def test_payload_head(terminal_total_difficulty: int, total: int, parent_total: int) -> None:
    """A payload on a block of proof of work is valid exactly when that block is terminal."""
    tree = [_pow(1, 0, total, parent_total), _payload(2, 1)]
    response = _update(tree, 2, terminal_total_difficulty=terminal_total_difficulty)
    if _is_terminal(terminal_total_difficulty, total, parent_total):
        assert response == _status("VALID", _hash(2))
    else:
        assert response == NOT_TERMINAL


def test_not_terminal_before_invalid() -> None:
    """An invalid payload above a block that is not terminal answers zero, not its valid parent."""
    # Payload 2 is valid, so a check of validity first would answer its hash instead.
    tree = [_pow(1, 0, 95, 90), _payload(2, 1), _payload(3, 2, valid=False)]
    assert _update(tree, 3, terminal_total_difficulty=100) == NOT_TERMINAL


def test_not_terminal_with_attributes() -> None:
    """A head that is not terminal starts no build, and its attributes are not read."""
    tree = [_pow(1, 0, 95, 90)]
    response = _update(tree, 1, terminal_total_difficulty=100, attributes={"timestamp": "0x1"})
    assert response == NOT_TERMINAL


def test_nearest_proof_of_work_block() -> None:
    """Only the most recent block of proof of work on the chain of the head is checked."""
    # Block 1 is not terminal, but its child 2 is, and payload 3 builds on block 2.
    tree = [_pow(1, 0, 95, 90), _pow(2, 1, 105, 95), _payload(3, 2)]
    assert _update(tree, 3, terminal_total_difficulty=100) == _status("VALID", _hash(3))


def test_latest_valid_block_of_proof_of_work() -> None:
    """An invalid payload on a terminal block answers zero, since that block is of proof of work."""
    tree = [_pow(1, 0, 105, 90), _payload(2, 1, valid=False)]
    assert _update(tree, 2, terminal_total_difficulty=100) == _status("INVALID", ZERO)


def test_latest_valid_payload() -> None:
    """An invalid payload on a valid payload answers that payload as its latest valid hash."""
    tree = [_pow(1, 0, 105, 90), _payload(2, 1), _payload(3, 2, valid=False)]
    assert _update(tree, 3, terminal_total_difficulty=100) == _status("INVALID", _hash(2))


def test_no_proof_of_work_block() -> None:
    """A tree with no block of proof of work passes the check, whatever the configuration."""
    tree = [_payload(2, 1)]
    for terminal_total_difficulty in [0, 100, 2**256 - 1]:
        response = _update(tree, 2, terminal_total_difficulty=terminal_total_difficulty)
        assert response == _status("VALID", _hash(2))


@pytest.mark.parametrize("version", [1, 2])
def test_versions(version: int) -> None:
    """Versions 1 and 2 of the method run the same terminal check and the same zero rule."""
    tree = [_pow(1, 0, 95, 90), _pow(2, 0, 105, 90), _payload(3, 2), _payload(4, 3)]
    method = f"engine_forkchoiceUpdatedV{version}"

    def update(head: int, known_finalized: str | None) -> dict:
        state = {"headBlockHash": _hash(head), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
        return engine.forkchoice_updated(
            CONFIG, tree, method, [state, None], known_finalized, terminal_total_difficulty=100
        )

    assert update(1, None) == NOT_TERMINAL
    assert update(4, None) == _status("VALID", _hash(4))
    with raises(engine.EngineError, INVALID_STATE) as error:
        update(4, _hash(3))
    assert error.value.code == 38002


def test_transition_build() -> None:
    """Attributes on a terminal head start the build of the first payload of proof of stake."""
    tree = [_pow(1, 0, 105, 90)]
    attributes = {
        "timestamp": "0x14",
        "prevRandao": ZERO,
        "suggestedFeeRecipient": "0x" + "00" * 20,
    }
    response = _update(tree, 1, terminal_total_difficulty=100, attributes=attributes)
    assert response["payloadStatus"] == _status("VALID", _hash(1))["payloadStatus"]
    # A payload ID is 8 bytes.
    assert len(bytes.fromhex(response["payloadId"].removeprefix("0x"))) == 8


# The tree of the transition: block 1 is terminal, and payloads 2 and 3 follow it.
TRANSITION_TREE = [_pow(1, 0, 105, 90), _payload(2, 1), _payload(3, 2)]


@pytest.mark.parametrize(
    "safe, finalized",
    [(ZERO, ZERO), (ZERO, _hash(2)), (_hash(2), ZERO)],
    ids=["both", "safe", "finalized"],
)
def test_zero_after_transition(safe: str, finalized: str) -> None:
    """Once the known finalized block is a payload, a zero safe or finalized hash is refused."""
    with raises(engine.EngineError, INVALID_STATE) as error:
        _update(
            TRANSITION_TREE,
            3,
            terminal_total_difficulty=100,
            safe=safe,
            finalized=finalized,
            known_finalized=_hash(2),
        )
    assert error.value.code == 38002


@pytest.mark.parametrize(
    "known_finalized", [None, _hash(1), _hash(9)], ids=["none", "pow", "unknown"]
)
def test_zero_before_transition(known_finalized: str | None) -> None:
    """Until a payload is finalized, zero safe and finalized hashes are accepted."""
    # No known finalized block, a finalized block of proof of work, and one the tree lacks.
    response = _update(
        TRANSITION_TREE, 3, terminal_total_difficulty=100, known_finalized=known_finalized
    )
    assert response == _status("VALID", _hash(3))


def test_nonzero_after_transition() -> None:
    """After the transition, safe and finalized blocks on the chain of the head are accepted."""
    response = _update(
        TRANSITION_TREE,
        3,
        terminal_total_difficulty=100,
        safe=_hash(3),
        finalized=_hash(2),
        known_finalized=_hash(2),
    )
    assert response == _status("VALID", _hash(3))


def test_below_finalized_after_transition() -> None:
    """A head below the known finalized block skips the update, so zero hashes are not read."""
    response = _update(TRANSITION_TREE, 2, terminal_total_difficulty=100, known_finalized=_hash(3))
    assert response == _status("VALID", _hash(2))


@pytest.mark.parametrize("name", ["totalDifficulty", "parentTotalDifficulty"])
def test_one_total_only(name: str) -> None:
    """A block of the tree with one total difficulty and not the other is malformed input."""
    block = _pow(1, 0, 105, 90)
    del block[name]
    with raises(engine.EngineError, "tree: one total difficulty without the other") as error:
        _update([block], 1, terminal_total_difficulty=100)
    assert error.value.code == 0


def test_terminal_total_difficulty_above_256_bits() -> None:
    """A terminal total difficulty of 2^256 does not fit the configuration."""
    with raises(
        engine.EngineError, f"config: a terminal total difficulty of {2**256}, not below 2^256"
    ) as error:
        _update([_pow(1, 0, 105, 90)], 1, terminal_total_difficulty=2**256)
    assert error.value.code == 0
