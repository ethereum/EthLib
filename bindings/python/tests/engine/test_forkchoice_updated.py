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


# The attributes of each version of their structure, with valid values.
ATTRIBUTES_V1 = {
    "timestamp": "0x1",
    "prevRandao": "0x" + "00" * 32,
    "suggestedFeeRecipient": "0x" + "00" * 20,
}
WITHDRAWAL = {"index": "0x0", "validatorIndex": "0x1", "address": "0x" + "11" * 20, "amount": "0x2"}
ATTRIBUTES_V2 = ATTRIBUTES_V1 | {"withdrawals": [WITHDRAWAL]}
ATTRIBUTES_V3 = ATTRIBUTES_V2 | {"parentBeaconBlockRoot": ZERO}
ATTRIBUTES_V4 = ATTRIBUTES_V3 | {"slotNumber": "0x1", "targetGasLimit": "0x1c9c380"}
# Block 3 is the tip of the valid chain, so an update to it selects a new valid head.
NEW_HEAD = {"headBlockHash": _hash(3), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
# Custody of all 128 columns, one bit each.
CUSTODY_COLUMNS = "0x" + "ff" * 16


# Valid attributes show that no build starts, and partial ones that they are not read.
OFF_HEAD_ATTRIBUTES = pytest.mark.parametrize(
    "attributes", [ATTRIBUTES_V1, {"timestamp": "0x1"}], ids=["valid", "partial"]
)


@pytest.mark.parametrize(
    ("version", "attributes"),
    [
        pytest.param(1, ATTRIBUTES_V1, id="v1"),
        pytest.param(2, ATTRIBUTES_V1, id="v2-structure-1"),
        pytest.param(2, ATTRIBUTES_V2, id="v2"),
        # A field whose value is null counts as absent.
        pytest.param(2, ATTRIBUTES_V1 | {"withdrawals": None}, id="v2-null-withdrawals"),
        pytest.param(3, ATTRIBUTES_V3, id="v3"),
        pytest.param(4, ATTRIBUTES_V4, id="v4"),
    ],
)
def test_build_not_specified(version: int, attributes: dict[str, object]) -> None:
    """Attributes that the version takes, on a new valid head, ask for an unspecified build."""
    with raises(
        engine.EngineError, "payload attributes: building a payload is not specified"
    ) as error:
        engine.forkchoice_updated(
            TREE, f"engine_forkchoiceUpdatedV{version}", [NEW_HEAD, attributes]
        )
    assert error.value.code == 0


@pytest.mark.parametrize(
    ("version", "attributes"),
    [
        pytest.param(1, {"timestamp": "0x1"}, id="v1-timestamp-only"),
        pytest.param(1, ATTRIBUTES_V2, id="v1-structure-2"),
        pytest.param(2, ATTRIBUTES_V3, id="v2-structure-3"),
        pytest.param(3, ATTRIBUTES_V2, id="v3-structure-2"),
        pytest.param(3, ATTRIBUTES_V4, id="v3-structure-4"),
        pytest.param(3, ATTRIBUTES_V3 | {"parentBeaconBlockRoot": None}, id="v3-null-root"),
        pytest.param(4, ATTRIBUTES_V3, id="v4-structure-3"),
        pytest.param(
            4,
            {key: value for key, value in ATTRIBUTES_V4.items() if key != "slotNumber"},
            id="v4-no-slotNumber",
        ),
        pytest.param(4, ATTRIBUTES_V4 | {"timestamp": "0x01"}, id="v4-leading-zero"),
        pytest.param(4, ATTRIBUTES_V4 | {"withdrawals": {}}, id="v4-withdrawals-object"),
        pytest.param(
            4,
            ATTRIBUTES_V4
            | {"withdrawals": [{k: v for k, v in WITHDRAWAL.items() if k != "amount"}]},
            id="v4-withdrawal-no-amount",
        ),
    ],
)
def test_invalid_payload_attributes(version: int, attributes: dict[str, object]) -> None:
    """On an applied valid head, attributes that fit no structure of the version are invalid."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes"
    ) as error:
        engine.forkchoice_updated(
            TREE, f"engine_forkchoiceUpdatedV{version}", [NEW_HEAD, attributes]
        )
    assert error.value.code == 38003


@pytest.mark.parametrize(
    "params",
    [
        pytest.param([NEW_HEAD, None], id="no-custody"),
        pytest.param([NEW_HEAD, None, None], id="null-custody"),
        pytest.param([NEW_HEAD, None, CUSTODY_COLUMNS], id="all-columns"),
        pytest.param([NEW_HEAD, None, "0x" + "00" * 16], id="no-column"),
    ],
)
def test_version_4_without_attributes(params: list[object]) -> None:
    """Without attributes, version 4 answers as version 3, whatever the custody columns."""
    want = {
        "payloadStatus": {"status": "VALID", "latestValidHash": _hash(3), "validationError": None},
        "payloadId": None,
    }
    assert engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV3", [NEW_HEAD, None]) == want
    assert engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV4", params) == want


@pytest.mark.parametrize(
    ("attributes", "message", "code"),
    [
        pytest.param(
            ATTRIBUTES_V3,
            "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes",
            38003,
            id="invalid",
        ),
        pytest.param(
            ATTRIBUTES_V4, "payload attributes: building a payload is not specified", 0, id="build"
        ),
    ],
)
def test_custody_columns_with_attributes(
    attributes: dict[str, object], message: str, code: int
) -> None:
    """Custody columns that decode leave the answer to the attributes."""
    with raises(engine.EngineError, message) as error:
        engine.forkchoice_updated(
            TREE, "engine_forkchoiceUpdatedV4", [NEW_HEAD, attributes, CUSTODY_COLUMNS]
        )
    assert error.value.code == code


@pytest.mark.parametrize(
    ("custody", "reason"),
    [
        ("0x" + "ff" * 15, "custodyColumns: 15 bytes, not 16"),
        ("0x" + "ff" * 17, "custodyColumns: 17 bytes, not 16"),
        ("ff" * 16, "custodyColumns: no 0x marker"),
        (16, "custodyColumns: not a string"),
        ("0x" + "zz" * 16, "custodyColumns: not a hex digit"),
        # Hex digits must be lowercase, as in every byte string of the Engine API decoders.
        ("0x" + "FF" * 16, "custodyColumns: not a hex digit"),
    ],
)
def test_custody_columns_malformed(custody: object, reason: str) -> None:
    """Custody columns that are not 16 bytes of lowercase hex are an invalid parameter."""
    with raises(
        engine.EngineError, f'engine error: EthLib.Engine.EngineError.invalidParams "{reason}"'
    ) as error:
        engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV4", [NEW_HEAD, None, custody])
    assert error.value.code == 32602


@pytest.mark.parametrize(
    ("version", "params", "reason"),
    [
        (1, [NEW_HEAD, None, CUSTODY_COLUMNS], "params: got 3, expected 2"),
        (2, [NEW_HEAD, None, CUSTODY_COLUMNS], "params: got 3, expected 2"),
        (3, [NEW_HEAD, None, CUSTODY_COLUMNS], "params: got 3, expected 2"),
        (4, [NEW_HEAD, None, CUSTODY_COLUMNS, None], "params: got 4, expected 2 or 3"),
        (4, [NEW_HEAD], "params: got 1, expected 2 or 3"),
    ],
)
def test_wrong_parameter_count(version: int, params: list[object], reason: str) -> None:
    """Versions 1 to 3 take two parameters, and version 4 two or three."""
    with raises(
        engine.EngineError, f'engine error: EthLib.Engine.EngineError.invalidParams "{reason}"'
    ) as error:
        engine.forkchoice_updated(TREE, f"engine_forkchoiceUpdatedV{version}", params)
    assert error.value.code == 32602


def test_head_below_finalized() -> None:
    """A valid head below the known finalized block is valid, whatever its safe block."""
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


@OFF_HEAD_ATTRIBUTES
def test_attributes_below_finalized(attributes: dict[str, object]) -> None:
    """Below the known finalized block no build begins, so payload attributes give `VALID`."""
    state = {"headBlockHash": _hash(2), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(
        TREE, "engine_forkchoiceUpdatedV1", [state, attributes], finalized=_hash(3)
    )
    assert response == {
        "payloadStatus": {"status": "VALID", "latestValidHash": _hash(2), "validationError": None},
        "payloadId": None,
    }


@OFF_HEAD_ATTRIBUTES
def test_attributes_unknown_head(attributes: dict[str, object]) -> None:
    """An unknown head is syncing, and its payload attributes start no build."""
    state = {"headBlockHash": _hash(9), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV1", [state, attributes])
    assert response == {
        "payloadStatus": {"status": "SYNCING", "latestValidHash": None, "validationError": None},
        "payloadId": None,
    }


@OFF_HEAD_ATTRIBUTES
def test_attributes_invalid_head(attributes: dict[str, object]) -> None:
    """An invalid head stays invalid, and its payload attributes start no build."""
    state = {"headBlockHash": _hash(5), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV1", [state, attributes])
    assert response == {
        "payloadStatus": {
            "status": "INVALID",
            "latestValidHash": _hash(3),
            "validationError": None,
        },
        "payloadId": None,
    }


@OFF_HEAD_ATTRIBUTES
def test_attributes_inconsistent_state(attributes: dict[str, object]) -> None:
    """An inconsistent forkchoice state fails before its payload attributes start a build."""
    state = {"headBlockHash": _hash(2), "safeBlockHash": _hash(3), "finalizedBlockHash": ZERO}
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidForkchoiceState"
    ) as error:
        engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV1", [state, attributes])
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


def test_duplicate_block_hash() -> None:
    """A tree with two payloads of one block hash is malformed input, with code 0."""
    tree = [*TREE, {"blockHash": _hash(2), "parentHash": _hash(1), "valid": False}]
    state = {"headBlockHash": _hash(3), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    with raises(engine.EngineError, "tree: two payloads with one block hash") as error:
        engine.forkchoice_updated(tree, "engine_forkchoiceUpdatedV3", [state, None])
    assert error.value.code == 0


@pytest.mark.parametrize("attributes", [1, "0x1", [], True], ids=repr)
@pytest.mark.parametrize("head", [3, 9], ids=["new-head", "unknown-head"])
@pytest.mark.parametrize("version", [1, 2, 3, 4])
def test_attributes_not_an_object(attributes: object, head: int, version: int) -> None:
    """Payload attributes that are neither an object nor null are an invalid parameter."""
    # Block 3 is a new valid head, and block 9 an unknown one that would answer syncing.
    state = {"headBlockHash": _hash(head), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "payloadAttributes: not an object"',
    ) as error:
        engine.forkchoice_updated(TREE, f"engine_forkchoiceUpdatedV{version}", [state, attributes])
    assert error.value.code == 32602


def test_bad_state_and_attributes() -> None:
    """A bad forkchoice state and bad payload attributes together report the state."""
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "forkchoiceState: not an object"',
    ) as error:
        engine.forkchoice_updated(TREE, "engine_forkchoiceUpdatedV3", [1, 1])
    assert error.value.code == 32602
