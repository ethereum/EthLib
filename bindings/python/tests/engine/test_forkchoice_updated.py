"""The head that engine_forkchoiceUpdated selects, on chains of the engine blockchain tests."""

import json
from collections.abc import Mapping
from pathlib import Path

import pytest

from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from raising import raises

from .cases import (
    BLOCK_FORKS,
    DEPOSIT_CONTRACT_ADDRESS,
    MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    TIME_FORKS,
    config,
)

_FILE = Path(__file__).resolve().parents[4] / "tests" / "engine" / "forkchoice.json"
CHAINS = json.loads(_FILE.read_text())

ZERO = "0x" + "00" * 32

INVALID_STATE = "engine error: EthLib.Engine.EngineError.invalidForkchoiceState"
UNSUPPORTED_FORK = "engine error: EthLib.Engine.EngineError.unsupportedFork"


def _hash(n: int) -> str:
    return "0x" + n.to_bytes(32, "big").hex()


def _known(block: str, parent: str, number: str, timestamp: str, *, valid: bool = True) -> dict:
    # The genesis headers of the fixtures write 0 as `0x00`, which is no Engine API quantity.
    return {
        "blockHash": block,
        "parentHash": parent,
        "valid": valid,
        "number": hex(int(number, 16)),
        "timestamp": hex(int(timestamp, 16)),
    }


# Every fork by block activates at block 0, then each fork by time 100 seconds after the last.
# So Shapella starts at 100, Dencun at 200, BPO2 at 600 and Glamsterdam at 700.
CONFIG = {
    "chainId": 1,
    "depositContractAddress": DEPOSIT_CONTRACT_ADDRESS,
    "activations": [[fork, "block", 0] for fork in BLOCK_FORKS]
    + [[fork, "time", 100 * (i + 1)] for i, fork in enumerate(TIME_FORKS)],
}


def _update(
    chain_config: dict,
    tree: list,
    head: str,
    safe: str = ZERO,
    finalized: str = ZERO,
    method: str = "engine_forkchoiceUpdatedV3",
) -> dict:
    state = {"headBlockHash": head, "safeBlockHash": safe, "finalizedBlockHash": finalized}
    return engine.forkchoice_updated(
        chain_config,
        tree,
        method,
        [state, None],
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )


@pytest.mark.parametrize("chain", CHAINS, ids=lambda c: f"{c['network']}-{c['test'][-60:]}")
def test_chain(chain: dict) -> None:
    """Each valid payload becomes the head, and the last head is the fixture's last block.

    Each response also reads back as its status and no payload ID.
    """
    genesis = chain["genesisHash"]
    chain_config = config(chain["network"])
    tree = [_known(genesis, ZERO, chain["genesisNumber"], chain["genesisTimestamp"])]
    head = genesis
    for payload in chain["payloads"]:
        method = f"engine_forkchoiceUpdatedV{payload['forkchoiceUpdatedVersion']}"
        if not payload["valid"]:
            # An invalid payload never joins the tree, so a head on it is unknown.
            response = _update(chain_config, tree, payload["blockHash"], method=method)
            assert response["payloadStatus"]["status"] == "SYNCING"
            assert engine.read_forkchoice_response(response) == ("SYNCING", None, None, None)
            continue
        tree.append(
            _known(
                payload["blockHash"], payload["parentHash"], payload["number"], payload["timestamp"]
            )
        )
        # The genesis block is final, so it is both the safe and the finalized block.
        response = _update(chain_config, tree, payload["blockHash"], genesis, genesis, method)
        assert response == {
            "payloadStatus": {
                "status": "VALID",
                "latestValidHash": payload["blockHash"],
                "validationError": None,
            },
            "payloadId": None,
        }
        block_hash = bytes.fromhex(payload["blockHash"].removeprefix("0x"))
        assert engine.read_forkchoice_response(response) == ("VALID", block_hash, None, None)
        head = payload["blockHash"]
    assert head == chain["lastblockhash"]


# A tree of five blocks: 1 <- 2 <- 3 is valid, 4 is an invalid child of 3, and 5 a child of 4.
# Block n has number n and timestamp 10 n, so all five are of Paris.
TREE = [
    _known(_hash(n), _hash(n - 1) if n > 1 else ZERO, hex(n), hex(10 * n), valid=n <= 3)
    for n in range(1, 6)
]


def test_invalid_head() -> None:
    """An invalid head is invalid, with the latest valid block of its chain."""
    status = _update(CONFIG, TREE, _hash(5))["payloadStatus"]
    assert (status["status"], status["latestValidHash"]) == ("INVALID", _hash(3))


def test_safe_off_chain() -> None:
    """A safe block that is not on the chain of the head is an invalid forkchoice state."""
    with raises(engine.EngineError, f"{INVALID_STATE} {_hash(3)} {ZERO}") as error:
        _update(CONFIG, TREE, _hash(2), safe=_hash(3))
    assert error.value.code == 38002


def test_finalized_unknown() -> None:
    """A finalized block that the tree does not hold is not on the chain of the head."""
    with raises(engine.EngineError, f"{INVALID_STATE} {ZERO} {_hash(9)}") as error:
        _update(CONFIG, TREE, _hash(3), finalized=_hash(9))
    assert error.value.code == 38002


def test_ancestors() -> None:
    """A safe and a finalized block among the ancestors of the head are accepted."""
    status = _update(CONFIG, TREE, _hash(3), safe=_hash(2), finalized=_hash(1))["payloadStatus"]
    assert status["status"] == "VALID"


def test_wrong_fields() -> None:
    """A forkchoice state with a missing field is an invalid parameter."""
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "forkchoiceState: wrong fields"',
    ) as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV3",
            [{"headBlockHash": _hash(3), "safeBlockHash": ZERO}, None],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 32602


# The attributes of each version of their structure, with valid values.
# Each timestamp is above the 30 seconds of block 3, in the fork of its structure.
ATTRIBUTES_V1 = {
    "timestamp": "0x32",
    "prevRandao": "0x" + "00" * 32,
    "suggestedFeeRecipient": "0x" + "00" * 20,
}
WITHDRAWAL = {"index": "0x0", "validatorIndex": "0x1", "address": "0x" + "11" * 20, "amount": "0x2"}
ATTRIBUTES_V2 = ATTRIBUTES_V1 | {"timestamp": "0x64", "withdrawals": [WITHDRAWAL]}
ATTRIBUTES_V3 = ATTRIBUTES_V2 | {"timestamp": "0xc8", "parentBeaconBlockRoot": ZERO}
ATTRIBUTES_V4 = ATTRIBUTES_V3 | {
    "timestamp": "0x2bc",
    "slotNumber": "0x1",
    "targetGasLimit": "0x1c9c380",
}
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
        # Version 3 takes the forks from Dencun on, before Glamsterdam: here BPO2, at 600 seconds.
        pytest.param(3, ATTRIBUTES_V3 | {"timestamp": "0x258"}, id="v3-at-bpo2"),
        # The last second before Shapella is still Paris.
        pytest.param(1, ATTRIBUTES_V1 | {"timestamp": "0x63"}, id="v1-before-shapella"),
        pytest.param(4, ATTRIBUTES_V4, id="v4"),
    ],
)
def test_build_starts(version: int, attributes: dict[str, object]) -> None:
    """Attributes that the version takes, on a new valid head, start a build named by its ID."""
    response = engine.forkchoice_updated(
        CONFIG,
        TREE,
        f"engine_forkchoiceUpdatedV{version}",
        [NEW_HEAD, attributes],
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
    assert response == {
        "payloadStatus": {"status": "VALID", "latestValidHash": _hash(3), "validationError": None},
        "payloadId": _payload_id(_hash(3), attributes),
    }


def _payload_id(head: str, attributes: Mapping[str, object]) -> str:
    """EthLib's payload ID: the first 8 bytes of the Keccak-256 hash of the head and attributes."""

    def raw(value: object) -> bytes:
        return bytes.fromhex(str(value).removeprefix("0x"))

    def word(value: object) -> bytes:
        return int(str(value), 16).to_bytes(8, "big")

    data = raw(head) + word(attributes["timestamp"]) + raw(attributes["prevRandao"])
    data += raw(attributes["suggestedFeeRecipient"])
    if "inclusionListTransactions" in attributes:
        transactions = attributes["inclusionListTransactions"]
        assert isinstance(transactions, list)
        for transaction in transactions:
            # A byte 1 before each byte of a transaction, and a byte 0 after it, mark its end.
            data += b"".join(bytes([1, byte]) for byte in raw(transaction)) + b"\x00"
        # A byte 2 ends the list.
        data += b"\x02"
    withdrawals = attributes.get("withdrawals") or []
    assert isinstance(withdrawals, list)
    for withdrawal in withdrawals:
        assert isinstance(withdrawal, dict)
        data += word(withdrawal["index"]) + word(withdrawal["validatorIndex"])
        data += raw(withdrawal["address"]) + word(withdrawal["amount"])
    if attributes.get("parentBeaconBlockRoot") is not None:
        data += raw(attributes["parentBeaconBlockRoot"])
    if "slotNumber" in attributes:
        data += word(attributes["slotNumber"]) + word(attributes["targetGasLimit"])
    return "0x" + keccak256(data)[:8].hex()


def test_payload_id_reads_each_attribute() -> None:
    """Two builds whose attributes differ in one field have different IDs."""
    ids = {
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV4",
            [NEW_HEAD, attributes],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )["payloadId"]
        for attributes in [
            ATTRIBUTES_V4,
            ATTRIBUTES_V4 | {"timestamp": "0x2bd"},
            ATTRIBUTES_V4 | {"prevRandao": "0x" + "01" * 32},
            ATTRIBUTES_V4 | {"suggestedFeeRecipient": "0x" + "01" * 20},
            ATTRIBUTES_V4 | {"withdrawals": []},
            ATTRIBUTES_V4 | {"parentBeaconBlockRoot": _hash(1)},
            ATTRIBUTES_V4 | {"slotNumber": "0x2"},
            ATTRIBUTES_V4 | {"targetGasLimit": "0x1c9c381"},
        ]
    }
    assert len(ids) == 8


@pytest.mark.parametrize(
    ("version", "attributes"),
    [
        pytest.param(1, {"timestamp": "0x32"}, id="v1-timestamp-only"),
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
            CONFIG,
            TREE,
            f"engine_forkchoiceUpdatedV{version}",
            [NEW_HEAD, attributes],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38003


@pytest.mark.parametrize(
    "params",
    [
        pytest.param([NEW_HEAD], id="no-attributes"),
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
    assert (
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV3",
            [NEW_HEAD, None],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
        == want
    )
    assert (
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV4",
            params,
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
        == want
    )


@pytest.mark.parametrize("version", [1, 2, 3])
def test_attributes_omitted(version: int) -> None:
    """A request without the attributes answers as one with `null` attributes."""
    answers = [
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            f"engine_forkchoiceUpdatedV{version}",
            params,
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
        for params in ([NEW_HEAD], [NEW_HEAD, None])
    ]
    assert answers[0] == answers[1]
    assert answers[0]["payloadId"] is None


def test_custody_columns_with_invalid_attributes() -> None:
    """Custody columns that decode leave the answer to the attributes."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes"
    ) as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV4",
            [NEW_HEAD, ATTRIBUTES_V3, CUSTODY_COLUMNS],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38003


def test_custody_columns_with_build() -> None:
    """Custody columns that decode leave the payload ID of the build unchanged."""
    with_custody = [NEW_HEAD, ATTRIBUTES_V4, CUSTODY_COLUMNS]
    without = [NEW_HEAD, ATTRIBUTES_V4]
    response = engine.forkchoice_updated(
        CONFIG,
        TREE,
        "engine_forkchoiceUpdatedV4",
        with_custody,
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
    assert response == engine.forkchoice_updated(
        CONFIG,
        TREE,
        "engine_forkchoiceUpdatedV4",
        without,
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
    assert response["payloadId"] == _payload_id(_hash(3), ATTRIBUTES_V4)


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
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV4",
            [NEW_HEAD, None, custody],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 32602


@pytest.mark.parametrize(
    ("version", "params", "reason"),
    [
        (1, [NEW_HEAD, None, CUSTODY_COLUMNS], "params: got 3, expected 1 or 2"),
        (2, [NEW_HEAD, None, CUSTODY_COLUMNS], "params: got 3, expected 1 or 2"),
        (3, [NEW_HEAD, None, CUSTODY_COLUMNS], "params: got 3, expected 1 or 2"),
        (3, [], "params: got 0, expected 1 or 2"),
        (4, [NEW_HEAD, None, CUSTODY_COLUMNS, None], "params: got 4, expected 1 to 3"),
        (4, [], "params: got 0, expected 1 to 3"),
    ],
)
def test_wrong_parameter_count(version: int, params: list[object], reason: str) -> None:
    """Versions 1 to 3 take one or two parameters, and version 4 one to three."""
    with raises(
        engine.EngineError, f'engine error: EthLib.Engine.EngineError.invalidParams "{reason}"'
    ) as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            f"engine_forkchoiceUpdatedV{version}",
            params,
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 32602


def test_head_below_finalized() -> None:
    """A valid head below the known finalized block is valid, whatever its safe block."""
    state = {"headBlockHash": _hash(2), "safeBlockHash": _hash(3), "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(
        CONFIG,
        TREE,
        "engine_forkchoiceUpdatedV3",
        [state, None],
        finalized=_hash(3),
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
    assert response == {
        "payloadStatus": {"status": "VALID", "latestValidHash": _hash(2), "validationError": None},
        "payloadId": None,
    }


def test_head_at_finalized() -> None:
    """A head equal to the known finalized block is checked as any other head."""
    with raises(engine.EngineError, f"{INVALID_STATE} {_hash(9)} {ZERO}") as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV3",
            [
                {"headBlockHash": _hash(3), "safeBlockHash": _hash(9), "finalizedBlockHash": ZERO},
                None,
            ],
            finalized=_hash(3),
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38002


@OFF_HEAD_ATTRIBUTES
def test_attributes_below_finalized(attributes: dict[str, object]) -> None:
    """Below the known finalized block no build begins, so payload attributes give `VALID`."""
    state = {"headBlockHash": _hash(2), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(
        CONFIG,
        TREE,
        "engine_forkchoiceUpdatedV1",
        [state, attributes],
        finalized=_hash(3),
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
    assert response == {
        "payloadStatus": {"status": "VALID", "latestValidHash": _hash(2), "validationError": None},
        "payloadId": None,
    }


@OFF_HEAD_ATTRIBUTES
def test_attributes_unknown_head(attributes: dict[str, object]) -> None:
    """An unknown head is syncing, and its payload attributes start no build."""
    state = {"headBlockHash": _hash(9), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(
        CONFIG,
        TREE,
        "engine_forkchoiceUpdatedV1",
        [state, attributes],
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
    assert response == {
        "payloadStatus": {"status": "SYNCING", "latestValidHash": None, "validationError": None},
        "payloadId": None,
    }


@OFF_HEAD_ATTRIBUTES
def test_attributes_invalid_head(attributes: dict[str, object]) -> None:
    """An invalid head stays invalid, and its payload attributes start no build."""
    state = {"headBlockHash": _hash(5), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    response = engine.forkchoice_updated(
        CONFIG,
        TREE,
        "engine_forkchoiceUpdatedV1",
        [state, attributes],
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
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
    with raises(engine.EngineError, f"{INVALID_STATE} {_hash(3)} {ZERO}") as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV1",
            [state, attributes],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
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
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV3",
            [state, None],
            finalized="0x00",
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 0


def test_duplicate_block_hash() -> None:
    """A tree with two payloads of one block hash is malformed input, with code 0."""
    tree = [*TREE, _known(_hash(2), _hash(1), "0x2", "0x14", valid=False)]
    state = {"headBlockHash": _hash(3), "safeBlockHash": ZERO, "finalizedBlockHash": ZERO}
    with raises(engine.EngineError, "tree: two payloads with one block hash") as error:
        engine.forkchoice_updated(
            CONFIG,
            tree,
            "engine_forkchoiceUpdatedV3",
            [state, None],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
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
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            f"engine_forkchoiceUpdatedV{version}",
            [state, attributes],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 32602


def test_bad_state_and_attributes() -> None:
    """A bad forkchoice state and bad payload attributes together report the state."""
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "forkchoiceState: not an object"',
    ) as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            "engine_forkchoiceUpdatedV3",
            [1, 1],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 32602


@pytest.mark.parametrize(
    ("version", "attributes", "fork"),
    [
        pytest.param(1, ATTRIBUTES_V1 | {"timestamp": "0x64"}, "shapella", id="v1-at-shapella"),
        pytest.param(2, ATTRIBUTES_V2 | {"timestamp": "0xc8"}, "dencun", id="v2-at-dencun"),
        pytest.param(3, ATTRIBUTES_V3 | {"timestamp": "0x64"}, "shapella", id="v3-at-shapella"),
        pytest.param(
            3, ATTRIBUTES_V3 | {"timestamp": "0x2bc"}, "glamsterdam", id="v3-at-glamsterdam"
        ),
        pytest.param(4, ATTRIBUTES_V4 | {"timestamp": "0x258"}, "bpo2", id="v4-at-bpo2"),
        # Both the fork and the timestamp fail here, and the fork check runs first.
        pytest.param(
            4, ATTRIBUTES_V4 | {"timestamp": "0x1"}, "paris", id="v4-before-head-in-paris"
        ),
    ],
)
def test_attributes_unsupported_fork(
    version: int, attributes: dict[str, object], fork: str
) -> None:
    """Attributes whose timestamp falls in a fork that the version does not take are -38005."""
    with raises(engine.EngineError, f'{UNSUPPORTED_FORK} (some "{fork}")') as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            f"engine_forkchoiceUpdatedV{version}",
            [NEW_HEAD, attributes],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38005


@pytest.mark.parametrize(
    ("version", "attributes"),
    [
        # Version 2 takes the structure of version 1 before Shapella only.
        pytest.param(2, ATTRIBUTES_V1 | {"timestamp": "0x64"}, id="v2-structure-1-at-shapella"),
        # Null withdrawals count as absent, so these are of the structure of version 1.
        pytest.param(
            2, ATTRIBUTES_V2 | {"withdrawals": None}, id="v2-null-withdrawals-at-shapella"
        ),
        # It takes the structure of version 2 from Shapella only.
        pytest.param(2, ATTRIBUTES_V2 | {"timestamp": "0x32"}, id="v2-structure-2-at-paris"),
        # The timestamp must be above the 30 seconds of the head.
        pytest.param(1, ATTRIBUTES_V1 | {"timestamp": "0x1e"}, id="v1-at-head-time"),
        pytest.param(1, ATTRIBUTES_V1 | {"timestamp": "0x1"}, id="v1-before-head"),
    ],
)
def test_attributes_rejected_at_head(version: int, attributes: dict[str, object]) -> None:
    """Attributes of the wrong structure for their fork, or not after the head, are -38003."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes"
    ) as error:
        engine.forkchoice_updated(
            CONFIG,
            TREE,
            f"engine_forkchoiceUpdatedV{version}",
            [NEW_HEAD, attributes],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38003


def _paris_at(block: int) -> dict:
    """A chain whose forks before Paris start at block 0, and Paris at a later block."""
    activations = [[fork, "block", 0] for fork in BLOCK_FORKS[:-1]]
    return CONFIG | {"activations": [*activations, ["paris", "block", block]]}


def test_fork_of_the_next_block() -> None:
    """The fork of the attributes is that of the block after the head, number 4 here."""
    response = engine.forkchoice_updated(
        _paris_at(4),
        TREE,
        "engine_forkchoiceUpdatedV1",
        [NEW_HEAD, ATTRIBUTES_V1],
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )
    assert response["payloadId"] == _payload_id(_hash(3), ATTRIBUTES_V1)
    # With Paris at block 5, block 4 is of London, which version 1 does not take.
    with raises(engine.EngineError, f'{UNSUPPORTED_FORK} (some "london")') as error:
        engine.forkchoice_updated(
            _paris_at(5),
            TREE,
            "engine_forkchoiceUpdatedV1",
            [NEW_HEAD, ATTRIBUTES_V1],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38005


def test_attributes_of_no_fork() -> None:
    """Attributes of a block that no fork has reached yet give -38005."""
    config = CONFIG | {"activations": [["paris", "block", 5]]}
    with raises(engine.EngineError, f"{UNSUPPORTED_FORK} none") as error:
        engine.forkchoice_updated(
            config,
            TREE,
            "engine_forkchoiceUpdatedV1",
            [NEW_HEAD, ATTRIBUTES_V1],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38005


# Bogota, the execution side of Hegota, starts 100 seconds after Glamsterdam, at 800 seconds.
CONFIG_BOGOTA = CONFIG | {"activations": [*CONFIG["activations"], ["hegota", "time", 800]]}
# Version 5 of the attributes: version 4 and an inclusion list, here a typed transaction and `0x00`.
# The entry `0x00` decodes as no transaction, and the Engine API still takes it.
ATTRIBUTES_V5 = ATTRIBUTES_V4 | {
    "timestamp": "0x320",
    "inclusionListTransactions": ["0x02f8", "0x00"],
}
# The tree of five blocks, with the verdict of block 3 on its inclusion list.
TREE_BOGOTA = [
    block | {"inclusionListSatisfied": True} if block["blockHash"] == _hash(3) else block
    for block in TREE
]


def _update_v5(params: list[object], tree: list[dict] = TREE_BOGOTA) -> dict:
    return engine.forkchoice_updated(
        CONFIG_BOGOTA,
        tree,
        "engine_forkchoiceUpdatedV5",
        params,
        terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
    )


@pytest.mark.parametrize("attributes", [None, ATTRIBUTES_V5], ids=["no-build", "build"])
def test_version_5_valid_head(attributes: dict[str, object] | None) -> None:
    """Version 5 answers a status of version 2, with the verdict of the valid head."""
    payload_id = None if attributes is None else _payload_id(_hash(3), attributes)
    assert _update_v5([NEW_HEAD, attributes, CUSTODY_COLUMNS]) == {
        "payloadStatus": {
            "status": "VALID",
            "latestValidHash": _hash(3),
            "validationError": None,
            "inclusionListSatisfied": True,
        },
        "payloadId": payload_id,
    }


def test_version_5_invalid_head() -> None:
    """The verdict of a head that is not valid is `null`."""
    state = NEW_HEAD | {"headBlockHash": _hash(5)}
    assert _update_v5([state, None])["payloadStatus"] == {
        "status": "INVALID",
        "latestValidHash": _hash(3),
        "validationError": None,
        "inclusionListSatisfied": None,
    }


def test_version_5_valid_head_without_verdict() -> None:
    """A valid head must carry its verdict, which is an input of the export."""
    with raises(engine.EngineError, "tree: no inclusion list verdict for the valid head") as error:
        _update_v5([NEW_HEAD, None], TREE)
    assert error.value.code == 0


def test_payload_id_reads_the_inclusion_list() -> None:
    """Two lists that differ only in where one transaction ends give different IDs."""
    ids = {
        _update_v5([NEW_HEAD, ATTRIBUTES_V5 | {"inclusionListTransactions": transactions}])[
            "payloadId"
        ]
        for transactions in [[], ["0x0102"], ["0x01", "0x02"], ["0x", "0x0102"]]
    }
    assert len(ids) == 4


@pytest.mark.parametrize(
    ("method", "attributes", "fork"),
    [
        # Version 5 takes Hegota alone, and version 4 Glamsterdam alone.
        pytest.param("engine_forkchoiceUpdatedV5", ATTRIBUTES_V4, "glamsterdam", id="v5-at-gloas"),
        pytest.param(
            "engine_forkchoiceUpdatedV4",
            ATTRIBUTES_V4 | {"timestamp": "0x320"},
            "hegota",
            id="v4-at-bogota",
        ),
    ],
)
def test_version_5_fork(method: str, attributes: dict[str, object], fork: str) -> None:
    """Attributes of a fork that the version does not take are an unsupported fork."""
    structure = attributes | ({"inclusionListTransactions": []} if method.endswith("V5") else {})
    with raises(engine.EngineError, f'{UNSUPPORTED_FORK} (some "{fork}")') as error:
        engine.forkchoice_updated(
            CONFIG_BOGOTA,
            TREE_BOGOTA,
            method,
            [NEW_HEAD, structure],
            terminal_total_difficulty=MAINNET_TERMINAL_TOTAL_DIFFICULTY,
        )
    assert error.value.code == 38005


def test_version_5_structure() -> None:
    """Version 5 takes attributes of version 5 only."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes"
    ) as error:
        _update_v5([NEW_HEAD, ATTRIBUTES_V4 | {"timestamp": "0x320"}])
    assert error.value.code == 38003
