"""The head that engine_forkchoiceUpdated selects, on chains of the engine blockchain tests."""

import json
from pathlib import Path

import pytest

from ethlib import engine
from raising import raises

_FILE = Path(__file__).resolve().parents[4] / "tests" / "engine" / "forkchoice.json"
CHAINS = json.loads(_FILE.read_text())

ZERO = "0x" + "00" * 32


def _hash(n: int) -> str:
    return "0x" + n.to_bytes(32, "big").hex()


def _update(
    tree: list,
    head: str,
    safe: str = ZERO,
    finalized: str = ZERO,
    method: str = "engine_forkchoiceUpdatedV3",
) -> dict:
    state = {"headBlockHash": head, "safeBlockHash": safe, "finalizedBlockHash": finalized}
    return engine.forkchoice_updated(tree, method, [state, None])


@pytest.mark.parametrize("chain", CHAINS, ids=lambda c: f"{c['network']}-{c['test'][-60:]}")
def test_chain(chain: dict) -> None:
    """Each valid payload becomes the head, and the last head is the fixture's last block."""
    genesis = chain["genesisHash"]
    tree = [{"blockHash": genesis, "parentHash": ZERO, "valid": True}]
    head = genesis
    for payload in chain["payloads"]:
        method = f"engine_forkchoiceUpdatedV{payload['forkchoiceUpdatedVersion']}"
        if not payload["valid"]:
            # An invalid payload never joins the tree, so a head on it is unknown.
            response = _update(tree, payload["blockHash"], method=method)
            assert response["payloadStatus"]["status"] == "SYNCING"
            continue
        tree.append(
            {"blockHash": payload["blockHash"], "parentHash": payload["parentHash"], "valid": True}
        )
        # The genesis block is final, so it is both the safe and the finalized block.
        response = _update(tree, payload["blockHash"], genesis, genesis, method)
        assert response == {
            "payloadStatus": {
                "status": "VALID",
                "latestValidHash": payload["blockHash"],
                "validationError": None,
            },
            "payloadId": None,
        }
        head = payload["blockHash"]
    assert head == chain["lastblockhash"]


# A tree of five blocks: 1 <- 2 <- 3 is valid, 4 is an invalid child of 3, and 5 a child of 4.
TREE = [
    {"blockHash": _hash(1), "parentHash": ZERO, "valid": True},
    {"blockHash": _hash(2), "parentHash": _hash(1), "valid": True},
    {"blockHash": _hash(3), "parentHash": _hash(2), "valid": True},
    {"blockHash": _hash(4), "parentHash": _hash(3), "valid": False},
    {"blockHash": _hash(5), "parentHash": _hash(4), "valid": False},
]


def test_invalid_head() -> None:
    """An invalid head is invalid, with the latest valid block of its chain."""
    status = _update(TREE, _hash(5))["payloadStatus"]
    assert (status["status"], status["latestValidHash"]) == ("INVALID", _hash(3))


def test_safe_off_chain() -> None:
    """A safe block that is not on the chain of the head is an invalid forkchoice state."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidForkchoiceState"
    ) as error:
        _update(TREE, _hash(2), safe=_hash(3))
    assert error.value.code == 38002


def test_finalized_unknown() -> None:
    """A finalized block that the tree does not hold is not on the chain of the head."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidForkchoiceState"
    ) as error:
        _update(TREE, _hash(3), finalized=_hash(9))
    assert error.value.code == 38002


def test_ancestors() -> None:
    """A safe and a finalized block among the ancestors of the head are accepted."""
    status = _update(TREE, _hash(3), safe=_hash(2), finalized=_hash(1))["payloadStatus"]
    assert status["status"] == "VALID"


def test_wrong_fields() -> None:
    """A forkchoice state with a missing field is an invalid parameter."""
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "forkchoiceState: wrong fields"',
    ) as error:
        engine.forkchoice_updated(
            TREE,
            "engine_forkchoiceUpdatedV3",
            [{"headBlockHash": _hash(3), "safeBlockHash": ZERO}, None],
        )
    assert error.value.code == 32602


def test_payload_attributes() -> None:
    """Payload attributes ask for a payload build, which is not specified, so code 0."""
    state = {"headBlockHash": _hash(3), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    with raises(
        engine.EngineError, "payload attributes: building a payload is not specified"
    ) as error:
        engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV1", [state, {"timestamp": "0x1"}])
    assert error.value.code == 0


def test_head_below_finalized() -> None:
    """A valid head below the known finalized block is valid, and the request is not checked."""
    state = {"headBlockHash": _hash(2), "safeBlockHash": _hash(3), "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(
        TREE, "engine_forkchoiceUpdatedV3", [state, None], finalized=_hash(3)
    )
    assert response == {
        "payloadStatus": {"status": "VALID", "latestValidHash": _hash(2), "validationError": None},
        "payloadId": None,
    }


def test_head_at_finalized() -> None:
    """A head equal to the known finalized block is checked as any other head."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidForkchoiceState"
    ) as error:
        engine.forkchoice_updated(
            TREE,
            "engine_forkchoiceUpdatedV3",
            [
                {"headBlockHash": _hash(3), "safeBlockHash": _hash(9), "finalizedBlockHash": ZERO},
                None,
            ],
            finalized=_hash(3),
        )
    assert error.value.code == 38002


def test_finalized_not_a_hash() -> None:
    """A known finalized block that is not a hash of 32 bytes is an input error, with code 0."""
    state = {"headBlockHash": _hash(2), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    with raises(
        engine.EngineError,
        'finalized: EthLib.Engine.EngineError.invalidParams "finalized: 1 bytes, not 32"',
    ) as error:
        engine.forkchoice_updated(
            TREE, "engine_forkchoiceUpdatedV3", [state, None], finalized="0x00"
        )
    assert error.value.code == 0
