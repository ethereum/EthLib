"""The writers of Engine API parameters, against the requests of `tests/engine`."""

import json
from collections import Counter
from pathlib import Path

import pytest

from ethlib import engine
from raising import raises

_DIR = Path(__file__).resolve().parents[4] / "tests" / "engine"
PAYLOADS = json.loads((_DIR / "new_payload.json").read_text())
CHAINS = json.loads((_DIR / "forkchoice.json").read_text())
EXAMPLES = json.loads((_DIR / "openrpc.json").read_text())

_INVALID = "engine error: EthLib.Engine.EngineError.invalidParams "

# The examples that the decoder rejects, by name, with the message of the rejection.
REJECTED = {
    # The payload ID of these examples has 15 hex digits, not the 16 of 8 bytes.
    "engine_getPayloadV2 example": _INVALID + '"payloadId: odd number of hex digits"',
    "engine_getPayloadV3 example": _INVALID + '"payloadId: odd number of hex digits"',
    "engine_getPayloadV4 example": _INVALID + '"payloadId: odd number of hex digits"',
    "engine_getPayloadV5 example": _INVALID + '"payloadId: odd number of hex digits"',
    "engine_getPayloadV6 example": _INVALID + '"payloadId: odd number of hex digits"',
    # The payload of this example has no `slotNumber`, which ExecutionPayloadV4 requires.
    "engine_newPayloadV5 example": _INVALID + '"payload: not the fields of version 4"',
    # EthLib does not specify these two methods.
    "engine_exchangeCapabilities example": "no method engine_exchangeCapabilities",
    "engine_exchangeTransitionConfigurationV1 example": (
        "no method engine_exchangeTransitionConfigurationV1"
    ),
}


def _payload_id(case: dict) -> str:
    return f"{case['network']}-{Path(case['file']).stem}-{case['test'][-50:]}-{case['payload']}"


@pytest.mark.parametrize("case", PAYLOADS, ids=_payload_id)
def test_new_payload(case: dict) -> None:
    """Parameters that decode are written back unchanged, and the others are invalid parameters."""
    try:
        rewritten = engine.rewrite_params(case["method"], case["params"])
    except engine.EngineError as error:
        # Only a request that the fixture rejects as invalid parameters may fail to decode.
        assert (case["errorCode"], error.code) == ("-32602", 32602)
    else:
        assert rewritten == case["params"]


def _rejected(case: dict) -> bool:
    try:
        engine.rewrite_params(case["method"], case["params"])
    except engine.EngineError:
        return True
    return False


def test_new_payload_counts() -> None:
    """Of the 250 requests, 239 decode, and the decoder rejects the 11 others."""
    # 75 fixtures expect invalid parameters; 64 of them decode, and a later check rejects them.
    assert Counter(_rejected(c) for c in PAYLOADS) == {False: 239, True: 11}


def _updates(chain: dict) -> list[tuple[str, list]]:
    # Each payload as the head, with the genesis block as safe and finalized, and no attributes.
    genesis = chain["genesisHash"]
    return [
        (
            f"engine_forkchoiceUpdatedV{payload['forkchoiceUpdatedVersion']}",
            [
                {
                    "headBlockHash": payload["blockHash"],
                    "safeBlockHash": genesis,
                    "finalizedBlockHash": genesis,
                },
                None,
            ],
        )
        for payload in chain["payloads"]
    ]


@pytest.mark.parametrize("chain", CHAINS, ids=lambda c: f"{c['network']}-{c['test'][-60:]}")
def test_forkchoice_updated(chain: dict) -> None:
    """The forkchoice state of each payload of a chain is written back unchanged."""
    for method, params in _updates(chain):
        assert engine.rewrite_params(method, params) == params


def _example_id(case: dict) -> str:
    return case["example"].replace(" ", "-")


@pytest.mark.parametrize("case", EXAMPLES, ids=_example_id)
def test_openrpc_example(case: dict) -> None:
    """Each request example is written back unchanged, or rejected for the reason it lists."""
    message = REJECTED.get(case["example"])
    if message is None:
        assert engine.rewrite_params(case["method"], case["params"]) == case["params"]
    else:
        with raises(engine.EngineError, message):
            engine.rewrite_params(case["method"], case["params"])


def test_openrpc_rejections_exist() -> None:
    """The 25 examples have distinct names, and every rejection above names one of them."""
    names = [c["example"] for c in EXAMPLES]
    assert len(set(names)) == len(names) == 25
    assert set(REJECTED) <= set(names)


_STATE = {
    "headBlockHash": "0x" + "11" * 32,
    "safeBlockHash": "0x" + "22" * 32,
    "finalizedBlockHash": "0x" + "33" * 32,
}


def test_custody_columns() -> None:
    """From version 4 the custody columns are written back, and their absence as `null`."""
    custody = "0x" + "0f" * 16
    assert engine.rewrite_params("engine_forkchoiceUpdatedV4", [_STATE, None, custody]) == [
        _STATE,
        None,
        custody,
    ]
    assert engine.rewrite_params("engine_forkchoiceUpdatedV4", [_STATE, None]) == [
        _STATE,
        None,
        None,
    ]


def test_canonical_form() -> None:
    """Address hex in mixed case is written in lowercase."""
    attributes = {"timestamp": "0x5", "prevRandao": "0x" + "00" * 32}
    mixed = {**attributes, "suggestedFeeRecipient": "0xA94f5374Fce5edBC8E2a8697C15331677e6EbF0B"}
    lower = {**attributes, "suggestedFeeRecipient": "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"}
    assert engine.rewrite_params("engine_forkchoiceUpdatedV1", [_STATE, mixed]) == [_STATE, lower]


def test_leading_zero() -> None:
    """The decoder rejects a quantity with a leading zero."""
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "start: leading zero"',
    ) as error:
        engine.rewrite_params("engine_getPayloadBodiesByRangeV1", ["0x01", "0x2"])
    assert error.value.code == 32602


def test_unknown_method() -> None:
    """A method that EthLib does not read has code 0."""
    with raises(engine.EngineError, "no method engine_newPayloadV6") as error:
        engine.rewrite_params("engine_newPayloadV6", [])
    assert error.value.code == 0
