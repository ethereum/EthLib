"""The Relay API block submissions against the examples and documents of the relay specification."""

import hashlib
import json
import re
import struct
from collections.abc import Iterator
from functools import cache
from itertools import count
from pathlib import Path
from typing import Any, NamedTuple

import pytest

from ethlib import consensus
from ethlib.errors import SszError
from raising import raises

# The examples and the fork documents of the relay specification, pinned in tests/sources.toml.
RELAY = Path(__file__).resolve().parents[4] / "tests/consensus/relay_api"
# The forks of the relay specification, by their consensus version names, in order.
VERSIONS = ["bellatrix", "capella", "deneb", "electra", "fulu"]
# The key that the examples leave out of their bid traces, and a value that fills it.
MISSING = "proposer_pubkey"
PROPOSER = "0x" + "ab" * 48
# The SSZ widths of a bid trace, of an offset and of a signature.
BID_TRACE_SIZE = 236
OFFSET_SIZE = 4
SIGNATURE_SIZE = 96
ZERO = bytes(32)
# The bytes of a blob, and the forks whose example holds a blob of 32 bytes instead.
BLOB_SIZE = 131_072
SHORT_BLOBS = ["deneb", "electra"]


def _sha(data: bytes) -> bytes:
    """The SHA-256 digest of the bytes."""
    return hashlib.sha256(data).digest()


@cache
def _zero_root(depth: int) -> bytes:
    """The root of a tree of zero chunks of a depth."""
    return ZERO if depth == 0 else _sha(_zero_root(depth - 1) * 2)


def _merkleize(chunks: list[bytes], limit: int) -> bytes:
    """The root of chunks in a tree with room for `limit` of them, padded with zero chunks."""
    assert len(chunks) <= limit
    depth = max(limit - 1, 0).bit_length()
    layer = chunks or [ZERO]
    for level in range(depth):
        if len(layer) % 2:
            layer = [*layer, _zero_root(level)]
        layer = [_sha(layer[i] + layer[i + 1]) for i in range(0, len(layer), 2)]
    return layer[0]


def _mix_in_length(root: bytes, length: int) -> bytes:
    """A root with the length of its list mixed in."""
    return _sha(root + length.to_bytes(32, "little"))


def _pack(data: bytes) -> list[bytes]:
    """Bytes cut into chunks of 32, the last one padded with zeros."""
    return [data[i : i + 32].ljust(32, b"\0") for i in range(0, len(data), 32)]


class Relay(NamedTuple):
    """The custom types, constants and containers of the relay documents up to a fork."""

    types: dict[str, str]
    constants: dict[str, int]
    containers: dict[str, list[tuple[str, str]]]


TABLE_ROW = re.compile(r"^\|\s*`(\w+)`\s*\|\s*`([^`]+)`")
CLASS = re.compile(r"```python\nclass (\w+)\(Container\):\n(.*?)```", re.S)
FIELD = re.compile(r"^\s+(\w+): (.+?)\s*$", re.M)
UINT_CONSTANT = re.compile(r"(?:uint64\()?(?:2\*\*(\d+)|(\d+))\)?")


def _constant(text: str) -> int:
    """The value of a constant as the tables write it: `uint64(2**8)`, `2**5` or `uint64(1)`."""
    match = UINT_CONSTANT.fullmatch(text)
    assert match, text
    power, plain = match.groups()
    return 2 ** int(power) if power else int(plain)


@cache
def _relay(version: str) -> Relay:
    """The definitions of the relay specification at a fork, with those of earlier forks."""
    before = _relay(VERSIONS[VERSIONS.index(version) - 1]) if version != VERSIONS[0] else None
    types = dict(before.types) if before else {}
    constants = dict(before.constants) if before else {}
    containers = dict(before.containers) if before else {}
    text = (RELAY / "specs" / version / "builder.md").read_text()
    for section in re.split(r"^## ", text, flags=re.M):
        rows = [TABLE_ROW.match(line) for line in section.splitlines()]
        found = [(row[1], row[2]) for row in rows if row]
        if section.startswith("Custom types"):
            types.update(found)
        elif section.startswith("Constants"):
            constants.update((name, _constant(value)) for name, value in found)
    # A later block of the same name replaces the earlier one, as a modified container does.
    for name, body in CLASS.findall(text):
        lines = [line for line in body.splitlines() if line.strip()]
        fields = [FIELD.fullmatch(line) for line in lines if not line.strip().startswith("#")]
        # Every line of a body is a field or a comment, so no field is dropped unseen.
        assert fields and all(fields), name
        containers[name] = [(field[1], field[2]) for field in fields if field]
    return Relay(types, constants, containers)


def _limit(relay: Relay, text: str) -> int:
    """The value of a bound: a product of constants and numbers."""
    value = 1
    for factor in text.split("*"):
        factor = factor.strip()
        value *= int(factor) if factor.isdigit() else relay.constants[factor]
    return value


def _hex(value: str) -> bytes:
    """The bytes of a 0x-prefixed hex string."""
    assert value.startswith("0x")
    return bytes.fromhex(value[2:])


BYTES = re.compile(r"Bytes(\d+)")
GENERIC = re.compile(r"(\w+)\[(.+)\]")
# The widths of the integer types of the relay documents, in bytes.
UINTS = {"uint64": 8, "uint256": 32}


def _list_bound(relay: Relay, arguments: str) -> tuple[str, int]:
    """The element type and the bound of a list type."""
    element, bound = (part.strip() for part in arguments.split(",", 1))
    # A list of integers would need packing, which no restated container has.
    assert element not in UINTS, element
    return element, _limit(relay, bound)


def _root(relay: Relay, kind: str, value: Any) -> bytes:
    """The root of a JSON value under a type of the relay specification."""
    kind = relay.types.get(kind, kind)
    if kind in UINTS:
        number = int(value)
        assert 0 <= number < 2 ** (8 * UINTS[kind]), (kind, value)
        return number.to_bytes(32, "little")
    if match := BYTES.fullmatch(kind):
        data = _hex(value)
        assert len(data) == int(match[1])
        return _merkleize(_pack(data), (len(data) + 31) // 32)
    if kind in relay.containers:
        fields = relay.containers[kind]
        assert list(value) == [name for name, _ in fields], kind
        return _merkleize([_root(relay, field, value[name]) for name, field in fields], len(fields))
    match = GENERIC.fullmatch(kind)
    assert match, kind
    outer, arguments = match.groups()
    if outer == "ByteVector":
        data = _hex(value)
        assert len(data) == _limit(relay, arguments)
        return _merkleize(_pack(data), (len(data) + 31) // 32)
    if outer == "ByteList":
        data, bound = _hex(value), _limit(relay, arguments)
        assert len(data) <= bound
        return _mix_in_length(_merkleize(_pack(data), (bound + 31) // 32), len(data))
    assert outer == "List", kind
    element, bound = _list_bound(relay, arguments)
    if len(value) > bound:
        raise ValueError(f"{len(value)} items over the bound {bound}")
    roots = [_root(relay, element, item) for item in value]
    return _mix_in_length(_merkleize(roots, bound), len(roots))


def _stream(seed: int, length: int) -> bytes:
    """Bytes of a length that depend on a seed, from SHA-256 in counter mode."""
    blocks = (length + 31) // 32
    return b"".join(_sha(f"{seed}:{i}".encode()) for i in range(blocks))[:length]


def _distinct(relay: Relay, kind: str, counter: Iterator[int]) -> Any:
    """A JSON value of a type of the relay documents whose leaves all differ.

    Two fields read into each other's place then change the root.
    """
    kind = relay.types.get(kind, kind)
    if kind == "uint64":
        return str(next(counter))
    if kind == "uint256":
        # Beyond 64 bits, so that a 64-bit field cannot hold it.
        return str(2**64 + next(counter))
    if match := BYTES.fullmatch(kind):
        return "0x" + _stream(next(counter), int(match[1])).hex()
    if kind in relay.containers:
        return {name: _distinct(relay, field, counter) for name, field in relay.containers[kind]}
    match = GENERIC.fullmatch(kind)
    assert match, kind
    outer, arguments = match.groups()
    if outer == "ByteVector":
        return "0x" + _stream(next(counter), _limit(relay, arguments)).hex()
    if outer == "ByteList":
        # Two chunks, so that the packing matters.
        return "0x" + _stream(next(counter), min(_limit(relay, arguments), 33)).hex()
    assert outer == "List", kind
    element, bound = _list_bound(relay, arguments)
    return [_distinct(relay, element, counter) for _ in range(min(bound, 2))]


def _example(version: str) -> dict[str, Any]:
    """The JSON value of the submission example of a fork."""
    path = RELAY / "examples" / version / "submit_block_request.json"
    return json.loads(path.read_text())["value"]


def _completed(version: str) -> dict[str, Any]:
    """The submission example of a fork, with the key that its bid trace lacks and full blobs."""
    example = _example(version)
    if "blobs_bundle" in example:
        bundle = example["blobs_bundle"]
        # A short blob is padded with zeros to the size of a blob.
        blobs = ["0x" + _hex(blob).ljust(BLOB_SIZE, b"\0").hex() for blob in bundle["blobs"]]
        example["blobs_bundle"] = {**bundle, "blobs": blobs}
    items = list(example["message"].items())
    # The source puts the key of the proposer after that of the builder.
    at = [key for key, _ in items].index("builder_pubkey") + 1
    example["message"] = dict([*items[:at], (MISSING, PROPOSER), *items[at:]])
    return example


def _fork(version: str) -> str:
    """The Lean fork of a consensus version."""
    return consensus.consensus_version_fork(version)


def _ssz(version: str, name: str, value: Any) -> bytes:
    """The SSZ bytes that EthLib reads from a JSON value of a container at a fork."""
    return consensus.api_ssz("mainnet", _fork(version), name, value)


def _json(version: str, name: str, data: bytes) -> dict[str, Any]:
    """The JSON that EthLib writes for the bytes of a container at a fork."""
    return consensus.api_json("mainnet", _fork(version), name, data)


def _lean_root(version: str, name: str, data: bytes) -> bytes:
    """The root that EthLib gives the bytes of a container, after checking they encode again."""
    root, again = consensus.ssz_static("mainnet", _fork(version), name, data)
    assert again == data
    return root


# The parts of a submission that the relay specification restates, with the fork they start at.
PARTS = [
    ("execution_payload", "ExecutionPayload", "bellatrix"),
    ("blobs_bundle", "BlobsBundle", "deneb"),
    ("execution_requests", "ExecutionRequests", "electra"),
]
# The size of the fixed part of a submission at each fork.
FIXED_SIZES = {"bellatrix": 336, "capella": 336, "deneb": 340, "electra": 344, "fulu": 344}
# The bound that the relay documents give the consolidation requests of a payload.
CONSOLIDATIONS = "MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD"
RELAY_CONSOLIDATIONS = 1
# The bound of the mainnet preset, written out so that the recorded defect stays visible.
PRESET_CONSOLIDATIONS = 2


def _parts(version: str) -> list[tuple[str, str]]:
    """The key and the container of each restated part that a submission holds at a fork."""
    return [
        (key, name)
        for key, name, first in PARTS
        if VERSIONS.index(first) <= VERSIONS.index(version)
    ]


def _with_preset_bound(relay: Relay) -> Relay:
    """The relay documents with the consolidation bound of the mainnet preset."""
    return relay._replace(constants={**relay.constants, CONSOLIDATIONS: PRESET_CONSOLIDATIONS})


@pytest.mark.parametrize("version", VERSIONS)
def test_example_parts(version: str):
    example = _example(version)
    assert list(example) == ["message", *(key for key, _ in _parts(version)), "signature"]
    for key, name in _parts(version):
        if name == "BlobsBundle" and version in SHORT_BLOBS:
            continue
        assert _json(version, name, _ssz(version, name, example[key])) == example[key]


@pytest.mark.parametrize("version", SHORT_BLOBS)
def test_example_short_blob_refused(version: str):
    bundle = _example(version)["blobs_bundle"]
    assert [len(_hex(blob)) for blob in bundle["blobs"]] == [32]
    message = f"document rejected: EthLib.Serialization.Ssz.Err.hexLength {BLOB_SIZE} 32"
    with raises(SszError, message):
        _ssz(version, "BlobsBundle", bundle)


@pytest.mark.parametrize("version", VERSIONS)
def test_example_bid_trace_refused(version: str):
    missing = f'document rejected: EthLib.Serialization.Ssz.Err.missingField "{MISSING}"'
    with raises(SszError, missing):
        _ssz(version, "BidTrace", _example(version)["message"])
    with raises(SszError, missing):
        _ssz(version, "SubmitBlockRequest", _example(version))


@pytest.mark.parametrize("fork", ["phase0", "altair", "glamsterdam"])
@pytest.mark.parametrize("name", ["BidTrace", "SubmitBlockRequest", "BuilderSubmitNewBlockRequest"])
def test_outside_relay_forks(fork: str, name: str):
    with raises(SszError, f"no container {name} at {fork}"):
        consensus.ssz_static("mainnet", fork, name, bytes(BID_TRACE_SIZE))


@pytest.mark.parametrize("version", VERSIONS)
def test_bid_trace_layout(version: str):
    relay = _relay(version)
    trace = _distinct(relay, "BidTrace", count(1))
    data = _ssz(version, "BidTrace", trace)
    assert len(data) == BID_TRACE_SIZE
    at = 0
    for name, kind in relay.containers["BidTrace"]:
        kind = relay.types.get(kind, kind)
        if kind in UINTS:
            width = UINTS[kind]
            assert data[at : at + width] == int(trace[name]).to_bytes(width, "little"), name
        else:
            width = len(_hex(trace[name]))
            assert data[at : at + width] == _hex(trace[name]), name
        at += width
    assert at == BID_TRACE_SIZE


@pytest.mark.parametrize("version", VERSIONS)
def test_submission_layout(version: str):
    submission = _completed(version)
    data = _ssz(version, "SubmitBlockRequest", submission)
    trace = _ssz(version, "BidTrace", submission["message"])
    parts = [_ssz(version, name, submission[key]) for key, name in _parts(version)]
    # The fixed part: the bid trace, one offset per variable part, then the signature.
    fixed = BID_TRACE_SIZE + OFFSET_SIZE * len(parts) + SIGNATURE_SIZE
    assert fixed == FIXED_SIZES[version]
    offsets = struct.unpack_from(f"<{len(parts)}I", data, BID_TRACE_SIZE)
    assert data[:BID_TRACE_SIZE] == trace
    assert data[fixed - SIGNATURE_SIZE : fixed] == _hex(submission["signature"])
    assert offsets[0] == fixed
    ends = [*offsets[1:], len(data)]
    assert [data[start:end] for start, end in zip(offsets, ends, strict=True)] == parts


@pytest.mark.parametrize("version", VERSIONS)
def test_submission_first_offset_refused(version: str):
    data = bytearray(_ssz(version, "SubmitBlockRequest", _completed(version)))
    fixed = FIXED_SIZES[version]
    struct.pack_into("<I", data, BID_TRACE_SIZE, fixed + 1)
    with raises(
        SszError, f"input rejected: EthLib.Serialization.Ssz.Err.firstOffset {fixed} {fixed + 1}"
    ):
        consensus.ssz_static("mainnet", _fork(version), "SubmitBlockRequest", bytes(data))


@pytest.mark.parametrize("version", VERSIONS)
def test_submission_root(version: str):
    submission = _completed(version)
    data = _ssz(version, "SubmitBlockRequest", submission)
    roots = [
        _lean_root(version, name, _ssz(version, name, submission[key]))
        for key, name in [("message", "BidTrace"), *_parts(version)]
    ]
    roots.append(_root(_relay(version), "BLSSignature", submission["signature"]))
    assert _lean_root(version, "SubmitBlockRequest", data) == _merkleize(roots, len(roots))


@pytest.mark.parametrize("version", VERSIONS)
def test_wrapped_submission(version: str):
    submission = _completed(version)
    data = _ssz(version, "SubmitBlockRequest", submission)
    wrapped = _ssz(version, "BuilderSubmitNewBlockRequest", {version: submission})
    # One variable-size field: its offset, then its bytes.
    assert wrapped == struct.pack("<I", OFFSET_SIZE) + data
    root = _lean_root(version, "SubmitBlockRequest", data)
    assert _lean_root(version, "BuilderSubmitNewBlockRequest", wrapped) == root
    assert _json(version, "BuilderSubmitNewBlockRequest", wrapped) == {
        version: _json(version, "SubmitBlockRequest", data)
    }
    field = [field for field, _ in _relay(version).containers["BuilderSubmitNewBlockRequest"]]
    assert field == [version]


@pytest.mark.parametrize(("version", "other"), list(zip(VERSIONS[1:], VERSIONS[:-1], strict=True)))
def test_wrapped_submission_other_fork_refused(version: str, other: str):
    wrapped = {other: _completed(version)}
    message = f'document rejected: EthLib.Serialization.Ssz.Err.undeclaredField "{other}"'
    with raises(SszError, message):
        _ssz(version, "BuilderSubmitNewBlockRequest", wrapped)


@pytest.mark.parametrize(
    ("version", "earlier", "field"),
    [
        ("deneb", "capella", "blobs_bundle"),
        ("electra", "deneb", "execution_requests"),
    ],
)
def test_submission_of_later_fork_refused(version: str, earlier: str, field: str):
    message = f'document rejected: EthLib.Serialization.Ssz.Err.undeclaredField "{field}"'
    with raises(SszError, message):
        _ssz(earlier, "SubmitBlockRequest", _completed(version))


def _restated(relay: Relay, version: str, name: str, value: Any) -> tuple[bytes, bytes]:
    """The roots of a restated container by the relay documents and by EthLib, with equal names."""
    data = _ssz(version, name, value)
    # The order of the keys of the JSON of EthLib carries no meaning; the roots check the order.
    assert sorted(field for field, _ in relay.containers[name]) == sorted(
        _json(version, name, data)
    )
    return _root(relay, name, value), _lean_root(version, name, data)


@pytest.mark.parametrize("version", VERSIONS)
def test_restated_containers_match(version: str):
    relay = _with_preset_bound(_relay(version))
    submission = _completed(version)
    fields = [field for field, _ in relay.containers["SubmitBlockRequest"]]
    assert fields == list(submission)
    examples = {
        "BidTrace": submission["message"],
        "SubmitBlockRequest": submission,
        **{name: submission[key] for key, name in _parts(version)},
    }
    for name, example in examples.items():
        for value in (example, _distinct(relay, name, count(1))):
            relay_root, lean_root = _restated(relay, version, name, value)
            assert relay_root == lean_root, name


@pytest.mark.parametrize("version", ["electra", "fulu"])
def test_restated_requests_differ(version: str):
    relay = _relay(version)
    assert relay.constants[CONSOLIDATIONS] == RELAY_CONSOLIDATIONS
    assert consensus.preset("mainnet")[CONSOLIDATIONS] == PRESET_CONSOLIDATIONS
    requests = _completed(version)["execution_requests"]
    relay_root, lean_root = _restated(relay, version, "ExecutionRequests", requests)
    # The bound sets the depth of the tree of the list, so the two roots differ.
    assert relay_root != lean_root
    # With the bound of the preset in place of that of the documents, the roots agree.
    assert _root(_with_preset_bound(relay), "ExecutionRequests", requests) == lean_root


@pytest.mark.parametrize("version", ["electra", "fulu"])
def test_two_consolidations(version: str):
    relay = _relay(version)
    requests = _completed(version)["execution_requests"]
    (consolidation,) = requests["consolidations"]
    two = {**requests, "consolidations": [consolidation] * PRESET_CONSOLIDATIONS}
    data = _ssz(version, "ExecutionRequests", two)
    assert _root(_with_preset_bound(relay), "ExecutionRequests", two) == _lean_root(
        version, "ExecutionRequests", data
    )
    # A relay that follows its documents refuses the requests that the consensus layer accepts.
    with raises(ValueError, f"{PRESET_CONSOLIDATIONS} items over the bound {RELAY_CONSOLIDATIONS}"):
        _root(relay, "ExecutionRequests", two)
    three = {**requests, "consolidations": [consolidation] * (PRESET_CONSOLIDATIONS + 1)}
    message = (
        "document rejected: EthLib.Serialization.Ssz.Err.documentOverLimit "
        f"{PRESET_CONSOLIDATIONS} {PRESET_CONSOLIDATIONS + 1}"
    )
    with raises(SszError, message):
        _ssz(version, "ExecutionRequests", three)


# The key under which the tests serve a bid: the relay source does not fix it.
RELAY_KEY = bytes(range(48))
# The fields of a payload that its header holds as roots, with the type of the list.
ROOTED = {
    "transactions": "List[Transaction, MAX_TRANSACTIONS_PER_PAYLOAD]",
    "withdrawals": "List[Withdrawal, MAX_WITHDRAWALS_PER_PAYLOAD]",
}


def _served(version: str, submission: dict[str, Any]) -> dict[str, Any]:
    """The JSON of the bid that EthLib serves from a submission under the key of the tests."""
    data = _ssz(version, "SubmitBlockRequest", submission)
    bid = consensus.relay_submission_bid("mainnet", _fork(version), data, RELAY_KEY)
    return _json(version, "BuilderBid", bid)


@pytest.mark.parametrize("version", VERSIONS)
def test_served_bid(version: str):
    relay = _with_preset_bound(_relay(version))
    for submission in (_completed(version), _distinct(relay, "SubmitBlockRequest", count(1))):
        served = _served(version, submission)
        payload = submission["execution_payload"]
        header = {key: value for key, value in payload.items() if key not in ROOTED}
        for key in ROOTED.keys() & payload.keys():
            header[f"{key}_root"] = "0x" + _root(relay, ROOTED[key], payload[key]).hex()
        assert served["header"] == header
        assert served["value"] == submission["message"]["value"]
        assert served["pubkey"] == "0x" + RELAY_KEY.hex()
        expected = {"header", "value", "pubkey"}
        if "blobs_bundle" in submission:
            assert served["blob_kzg_commitments"] == submission["blobs_bundle"]["commitments"]
            expected.add("blob_kzg_commitments")
        if "execution_requests" in submission:
            assert served["execution_requests"] == submission["execution_requests"]
            expected.add("execution_requests")
        assert set(served) == expected


@pytest.mark.parametrize("fork", ["altair", "glamsterdam"])
def test_served_bid_outside_relay_forks(fork: str):
    with raises(SszError, f"no Relay API submissions at {fork}"):
        consensus.relay_submission_bid("mainnet", fork, b"", RELAY_KEY)
