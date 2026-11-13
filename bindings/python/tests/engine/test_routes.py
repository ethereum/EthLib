"""The engine_newPayload vectors as beacon requests, through the method and the beacon engine."""

# A request of the beacon chain reaches the execution layer by two routes in EthLib.
# The beacon chain reads it directly, through its model of the execution layer.
# Between the two clients of a node it travels as the JSON parameters of engine_newPayload.
# The vectors hold no parent state, so both routes stop before the state transition.
# The method then answers SYNCING, and the model takes the transition as passed.

import json
import re
from pathlib import Path
from typing import Any

import pytest

from ethlib import engine
from raising import raises, shape_pattern

from .cases import FORK_OF_NETWORK, TRANSITION_TIME, check, config

_FILE = Path(__file__).resolve().parents[4] / "tests" / "engine" / "new_payload.json"
CASES = json.loads(_FILE.read_text())

# The forks of the beacon chain from Bellatrix, in order, as the export names them.
FORKS = ["bellatrix", "shapella", "dencun", "pectra", "fusaka", "bpo1", "bpo2", "glamsterdam"]

# The request types of the beacon chain, in their order, and the fork that adds each.
REQUEST_TYPES = {0: "pectra", 1: "pectra", 2: "pectra", 3: "glamsterdam", 4: "glamsterdam"}

# The message of the SSZ decoder for a list whose length is no whole number of elements.
UNDIVIDED = "input rejected: EthLib.Serialization.Ssz.Err.scopeUndivided {n} 192"

# A vector that expects invalid parameters is not one that the beacon chain can form.
FORMED = [c for c in CASES if c["errorCode"] is None]


def _since(fork: str, first: str) -> bool:
    """Whether `fork` is `first` or a later fork of the beacon chain."""
    return FORKS.index(fork) >= FORKS.index(first)


def _beacon_fork(network: str, timestamp: int) -> str:
    """The beacon fork at a timestamp of a network, such as `CancunToPragueAtTime15k`."""
    before, _, after = network.removesuffix("AtTime15k").partition("To")
    fork = FORK_OF_NETWORK[after if after and timestamp >= TRANSITION_TIME else before]
    # The beacon chain names its side of the merge Bellatrix.
    return "bellatrix" if fork == "paris" else fork


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def _uint(value: str, size: int) -> bytes:
    return int(value, 16).to_bytes(size, "little")


def _container(parts: list[tuple[bool, bytes]]) -> bytes:
    """The SSZ bytes of a container, from each field's bytes and whether it is variable in size."""
    fixed_size = sum(4 if variable else len(data) for variable, data in parts)
    head, tail = b"", b""
    for variable, data in parts:
        if variable:
            head += (fixed_size + len(tail)).to_bytes(4, "little")
            tail += data
        else:
            head += data
    return head + tail


def _byte_lists(items: list[bytes]) -> bytes:
    """The SSZ bytes of a list of byte lists: an offset for each, then their bytes."""
    return _container([(True, item) for item in items])


def _withdrawal(withdrawal: dict[str, str]) -> bytes:
    return (
        _uint(withdrawal["index"], 8)
        + _uint(withdrawal["validatorIndex"], 8)
        + _hex(withdrawal["address"])
        + _uint(withdrawal["amount"], 8)
    )


def _payload(fork: str, payload: dict[str, Any]) -> bytes:
    """The SSZ bytes of the beacon execution payload of a JSON payload."""
    parts = [
        (False, _hex(payload["parentHash"])),
        (False, _hex(payload["feeRecipient"])),
        (False, _hex(payload["stateRoot"])),
        (False, _hex(payload["receiptsRoot"])),
        (False, _hex(payload["logsBloom"])),
        (False, _hex(payload["prevRandao"])),
        (False, _uint(payload["blockNumber"], 8)),
        (False, _uint(payload["gasLimit"], 8)),
        (False, _uint(payload["gasUsed"], 8)),
        (False, _uint(payload["timestamp"], 8)),
        (True, _hex(payload["extraData"])),
        (False, _uint(payload["baseFeePerGas"], 32)),
        (False, _hex(payload["blockHash"])),
        (True, _byte_lists([_hex(tx) for tx in payload["transactions"]])),
    ]
    if _since(fork, "shapella"):
        parts.append((True, b"".join(_withdrawal(w) for w in payload["withdrawals"])))
    if _since(fork, "dencun"):
        parts.append((False, _uint(payload["blobGasUsed"], 8)))
        parts.append((False, _uint(payload["excessBlobGas"], 8)))
    if _since(fork, "glamsterdam"):
        parts.append((True, _hex(payload["blockAccessList"])))
        parts.append((False, _uint(payload["slotNumber"], 8)))
    return _container(parts)


def _requests(fork: str, encoded: list[str]) -> bytes | None:
    """The SSZ bytes of the beacon execution requests, or None when the lists fit no such value."""
    lists = {t: b"" for t, first in REQUEST_TYPES.items() if _since(fork, first)}
    previous = -1
    for item in map(_hex, encoded):
        # The beacon chain sends each nonempty list once, by increasing type.
        request_type = item[0] if item else -1
        if len(item) < 2 or request_type not in lists or request_type <= previous:
            return None
        previous = request_type
        lists[request_type] = item[1:]
    return _container([(True, data) for data in lists.values()])


def _request_ssz(fork: str, params: list[Any]) -> bytes | None:
    """The SSZ bytes of the beacon payload request of JSON parameters, or None when none fits."""
    parts = [(True, _payload(fork, params[0]))]
    if _since(fork, "dencun"):
        parts.append((True, b"".join(map(_hex, params[1]))))
        parts.append((False, _hex(params[2])))
    if _since(fork, "pectra"):
        requests = _requests(fork, params[3])
        if requests is None:
            return None
        parts.append((True, requests))
    return _container(parts)


def _id(case: dict[str, Any]) -> str:
    return f"{case['network']}-{Path(case['file']).stem}-{case['test'][-50:]}-{case['payload']}"


def _fork(case: dict[str, Any]) -> str:
    return _beacon_fork(case["network"], int(case["params"][0]["timestamp"], 16))


def _routes(case: dict[str, Any]) -> tuple[list[Any] | None, str | None, int | None, bool]:
    """Both routes for a vector that converts to a beacon request in SSZ."""
    fork = _fork(case)
    request = _request_ssz(fork, case["params"])
    assert request is not None
    return engine.new_payload_routes(config(case["network"]), "mainnet", fork, request)


def _kind(case: dict[str, Any]) -> str:
    """Whether the encoder refuses a vector, the decoder rejects its bytes, or both routes run."""
    fork = _fork(case)
    request = _request_ssz(fork, case["params"])
    if request is None:
        return "encoder"
    try:
        engine.new_payload_routes(config(case["network"]), "mainnet", fork, request)
    except engine.EngineError as error:
        # The bytes fit no request of the beacon chain: a list whose length is no whole number.
        assert error.code == 0
        assert re.fullmatch(shape_pattern(UNDIVIDED), str(error))
        return "decoder"
    return "routes"


@pytest.mark.parametrize("case", FORMED, ids=_id)
def test_routes_agree(case: dict[str, Any]) -> None:
    """The method passes the request before execution exactly when the beacon engine accepts it."""
    if _kind(case) != "routes":
        # Only request lists that the beacon chain never sends make a vector unformable.
        assert "BlockException.INVALID_REQUESTS" in (case["validationError"] or "").split("|")
        return
    params, status, code, accepted = _routes(case)
    # The JSON that EthLib writes is the vector itself.
    assert params == case["params"]
    assert code is None
    # The JSON route answers as the method of the vector does, at the version of the vector.
    direct = engine.new_payload(config(case["network"]), case["method"], case["params"])
    assert status == direct["status"]
    assert accepted == (status == "SYNCING")
    # The fixture is the oracle: only a payload that fails a check before execution is refused.
    kind = check(case["network"], case["method"], case["params"], case["validationError"], None)
    assert accepted == (kind != "invalid")


def test_counts() -> None:
    """Of 175 vectors, the encoder refuses 16 and the decoder 4, and 95 pass both routes."""
    kinds = [_kind(c) for c in FORMED]
    accepted = sum(_routes(c)[3] for c, kind in zip(FORMED, kinds, strict=True) if kind == "routes")
    # The 95 are the 93 valid payloads and the 2 that fail only when their block runs.
    assert (len(FORMED), kinds.count("encoder"), kinds.count("decoder"), accepted) == (
        175,
        16,
        4,
        95,
    )


@pytest.mark.parametrize(
    ("preset", "fork", "message"),
    [
        ("mainnet", "phase0", "no payload request at phase0"),
        ("mainnet", "hegota", "no version of engine_newPayload at hegota"),
        ("bogus", "pectra", "no preset is named bogus"),
    ],
)
def test_rejected_inputs(preset: str, fork: str, message: str) -> None:
    """A fork before Bellatrix or from Hegota, or an unknown preset, has code 0."""
    with raises(engine.EngineError, message) as error:
        engine.new_payload_routes(config("Prague"), preset, fork, b"")
    assert error.value.code == 0


def test_unsupported_fork() -> None:
    """A Bellatrix request on a chain at Shanghai is unsupported by the method and refused."""
    case = next(c for c in FORMED if c["network"] == "Paris" and c["validationError"] is None)
    request = _request_ssz("bellatrix", case["params"])
    assert request is not None
    result = engine.new_payload_routes(config("Shanghai"), "mainnet", "bellatrix", request)
    assert result == (case["params"], None, 38005, False)
