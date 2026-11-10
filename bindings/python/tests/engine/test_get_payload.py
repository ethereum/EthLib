"""The versions, fork checks and KZG bundle checks of engine_getPayload."""

# Rules: ethereum/execution-apis, src/engine/{paris,shanghai,cancun,prague,osaka,amsterdam}.md.
# Commit: 3284ee80c3da3e516c53782dde75157cccf1ebdc.
# Payloads: the pinned execution-specs fixtures in tests/engine/new_payload.json.
# Blob inputs: the pinned zero-polynomial KZG fixture; no expected value calls EthLib.

import hashlib
import json
import re
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest

from ethlib import engine
from ethlib.serialization import rlp
from raising import raises

from .cases import FORK_OF_NETWORK, config

_TESTS = Path(__file__).resolve().parents[4] / "tests"
_PAYLOADS = json.loads((_TESTS / "engine" / "new_payload.json").read_text())
_ZERO = dict(
    re.findall(
        r"^  (blob|commitment|proof): '([^']*)'",
        (
            _TESTS
            / "cryptography/kzg/verify_blob_kzg_proof"
            / "verify_blob_kzg_proof_case_correct_proof_point_at_infinity_for_zero_poly/data.yaml"
        ).read_text(),
        re.MULTILINE,
    )
)
ID = b"\x01" * 8
UNKNOWN = b"\x02" * 8
EMPTY_BUNDLE: dict[str, list] = {"blobs": [], "commitments": [], "proofs": []}
_VERSIONS = [
    (1, "Paris"),
    (2, "Paris"),
    (2, "Shanghai"),
    (3, "Cancun"),
    (4, "Prague"),
    (5, "Osaka"),
    (6, "Amsterdam"),
]


def _payload(network: str) -> dict:
    """A valid pinned payload whose transaction carries no blob."""
    return deepcopy(
        next(
            case["params"][0]
            for case in _PAYLOADS
            if case["network"] == network
            and case["validationError"] is None
            and case["errorCode"] is None
            and all(not tx.startswith("0x03") for tx in case["params"][0]["transactions"])
        )
    )


def _entry(
    network: str,
    payload: dict | None = None,
    sidecars: list[bytes] | None = None,
    requests: list[bytes] | None = None,
    override: bool = False,
) -> engine.PayloadEntry:
    """One snapshot entry, with a chosen value of 42 wei."""
    if requests is None and network in {"Prague", "Osaka", "Amsterdam"}:
        requests = []
    return (
        ID,
        FORK_OF_NETWORK[network],
        _payload(network) if payload is None else payload,
        42,
        sidecars or [],
        requests,
        override,
    )


def _call(
    network: str, version: int, entries: list[engine.PayloadEntry], identifier: bytes = ID
) -> dict:
    return engine.get_payload(
        config(network), entries, f"engine_getPayloadV{version}", ["0x" + identifier.hex()]
    )


@pytest.mark.parametrize(("version", "network"), _VERSIONS)
def test_version(version: int, network: str) -> None:
    """Each method returns exactly the fields of its version, preserving the payload."""
    payload = _payload(network)
    result = _call(network, version, [_entry(network, payload)])
    if version == 1:
        assert result == payload
        return
    expected: dict[str, Any] = {"executionPayload": payload, "blockValue": "0x2a"}
    if version >= 3:
        expected |= {"blobsBundle": EMPTY_BUNDLE, "shouldOverrideBuilder": False}
    if version >= 4:
        expected["executionRequests"] = []
    assert result == expected


@pytest.mark.parametrize(("version", "network"), _VERSIONS)
def test_unknown_payload(version: int, network: str) -> None:
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.unknownPayload") as e:
        _call(network, version, [_entry(network)], UNKNOWN)
    assert e.value.code == 38001


@pytest.mark.parametrize(
    ("version", "network"),
    [(1, "Shanghai"), (2, "Cancun"), (3, "Prague"), (4, "Osaka"), (5, "Amsterdam"), (6, "Osaka")],
)
def test_unsupported_fork(version: int, network: str) -> None:
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork") as e:
        _call(network, version, [_entry(network)])
    assert e.value.code == 38005


def test_timestamp_selects_fork() -> None:
    """A declared fork cannot override the fork selected by the payload timestamp."""
    entry = _entry("Cancun")
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork"):
        engine.get_payload(config("Prague"), [entry], "engine_getPayloadV3", ["0x" + ID.hex()])


def _bundle(network: str, count: int = 1) -> tuple[dict, list[bytes], dict]:
    """The pinned zero-polynomial bundle, with its type-3 transaction and network form."""
    blob = bytes.fromhex(_ZERO["blob"][2:])
    commitment = bytes.fromhex(_ZERO["commitment"][2:])
    proof = bytes.fromhex(_ZERO["proof"][2:])
    hashes = [b"\x01" + hashlib.sha256(commitment).digest()[1:]] * count
    body = [
        b"\x01",
        b"",
        b"\x01",
        b"\x0a",
        b"\x52\x08",
        b"\x11" * 20,
        b"",
        b"",
        [],
        b"\x01",
        hashes,
        b"",
        b"\x01",
        b"\x01",
    ]
    cell = network in {"Osaka", "Amsterdam"}
    proofs = [proof] * (128 * count if cell else count)
    fields = [body, *([b"\x01"] if cell else []), [blob] * count, [commitment] * count, proofs]
    sidecar = b"\x03" + rlp.encode(fields)
    payload = _payload(network)
    payload["transactions"] = ["0x03" + rlp.encode(body).hex()]
    expected = {
        "blobs": [_ZERO["blob"]] * count,
        "commitments": [_ZERO["commitment"]] * count,
        "proofs": [_ZERO["proof"]] * len(proofs),
    }
    return payload, [sidecar], expected


@pytest.mark.parametrize(
    ("version", "network"), [(3, "Cancun"), (4, "Prague"), (5, "Osaka"), (6, "Amsterdam")]
)
def test_bundle(version: int, network: str) -> None:
    """Blob proofs and all 128 cell proofs are returned only after their batch check passes."""
    payload, sidecars, expected = _bundle(network, count=2)
    result = _call(network, version, [_entry(network, payload, sidecars, override=True)])
    assert result["blobsBundle"] == expected
    assert result["executionPayload"] == payload
    assert result["shouldOverrideBuilder"] is True


@pytest.mark.parametrize(("version", "network"), [(3, "Cancun"), (5, "Osaka")])
def test_missing_blob(version: int, network: str) -> None:
    payload, _, _ = _bundle(network)
    with raises(engine.EngineError, "store: bundle error 102") as e:
        _call(network, version, [_entry(network, payload)])
    assert e.value.code == 0


def test_wrong_hash() -> None:
    payload, sidecars, _ = _bundle("Cancun")
    fields = rlp.decode(bytes.fromhex(payload["transactions"][0][4:]))
    fields[10] = [b"\x01" + b"\x00" * 31]
    payload["transactions"] = ["0x03" + rlp.encode(fields).hex()]
    with raises(engine.EngineError, "store: bundle error 103"):
        _call("Cancun", 3, [_entry("Cancun", payload, sidecars)])


@pytest.mark.parametrize(("version", "network"), [(3, "Cancun"), (5, "Osaka")])
def test_proof_rejected(version: int, network: str) -> None:
    payload, sidecars, _ = _bundle(network)
    fields = rlp.decode(sidecars[0][1:])
    # Constant one has a nonzero commitment, so the zero commitment and proof cannot open it.
    fields[-3] = [(b"\x00" * 31 + b"\x01") * 4096]
    sidecars = [b"\x03" + rlp.encode(fields)]
    with raises(engine.EngineError, "store: bundle error 105"):
        _call(network, version, [_entry(network, payload, sidecars)])


def test_wrong_cell_proof_count() -> None:
    payload, sidecars, _ = _bundle("Osaka")
    fields = rlp.decode(sidecars[0][1:])
    fields[-1] = fields[-1][:-1]
    with raises(engine.EngineError, "store: bundle error 102"):
        _call("Osaka", 5, [_entry("Osaka", payload, [b"\x03" + rlp.encode(fields)])])


@pytest.mark.parametrize("requests", [[b"\x00"], [b"\x01a", b"\x00b"], [b"\x00a", b"\x00b"]])
def test_bad_requests(requests: list[bytes]) -> None:
    with raises(engine.EngineError, "store: execution requests out of order or too short"):
        _call("Prague", 4, [_entry("Prague", requests=requests)])


def test_requests() -> None:
    requests = [b"\x00a", b"\x02b"]
    result = _call("Prague", 4, [_entry("Prague", requests=requests)])
    assert result["executionRequests"] == ["0x0061", "0x0262"]


@pytest.mark.parametrize("params", [[], ["0x00"], ["0x" + ID.hex(), "0x00"]])
def test_bad_params(params: list) -> None:
    message = (
        'engine error: EthLib.Engine.EngineError.invalidParams "payloadId: 1 bytes, not 8"'
        if len(params) == 1
        else "engine error: EthLib.Engine.EngineError.invalidParams "
        f'"params: got {len(params)}, expected 1"'
    )
    with raises(engine.EngineError, message) as e:
        engine.get_payload(config("Paris"), [], "engine_getPayloadV1", params)
    assert e.value.code == 32602


def test_duplicate_id() -> None:
    entry = _entry("Paris")
    with raises(engine.EngineError, "store: two entries with one payload ID"):
        _call("Paris", 1, [entry, entry])


def test_unknown_method() -> None:
    with raises(engine.EngineError, "no method engine_getPayloadV7"):
        engine.get_payload(config("Paris"), [], "engine_getPayloadV7", [])
