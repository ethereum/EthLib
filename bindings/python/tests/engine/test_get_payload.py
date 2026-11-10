"""The versions, fork checks and KZG bundle checks of engine_getPayload."""

# Rules: ethereum/execution-apis, src/engine/{paris,shanghai,cancun,prague,osaka,amsterdam}.md.
# Commit: 3284ee80c3da3e516c53782dde75157cccf1ebdc.
# Builds: the first block of the pinned blockchain test of each network, as test_build_payload.
# Blob inputs: the pinned KZG fixtures of verify_blob_kzg_proof; no expected value calls EthLib.
# Access list: the pinned Amsterdam payload of tests/engine/new_payload.json.

import functools
import hashlib
import json
from collections.abc import Callable
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from ethlib.execution import blocks
from ethlib.serialization import rlp
from raising import raises

from .cases import FORK_OF_NETWORK, config
from .test_build_payload import (
    COINBASE,
    EXTRA_DATA,
    GAS_LIMIT,
    METHODS,
    _attributes,
    _chain,
    _first_block,
    _payload_transaction,
)

_TESTS = Path(__file__).resolve().parents[4] / "tests"
_KZG = _TESTS / "cryptography" / "kzg" / "verify_blob_kzg_proof"
_PAYLOADS = json.loads((_TESTS / "engine" / "new_payload.json").read_text())

ID = b"\x01" * 8
UNKNOWN = b"\x02" * 8
TRANSACTIONS_ROOT, REQUESTS_HASH, BAL_HASH = 4, 20, 21
CELL_NETWORKS = {"Osaka", "Amsterdam"}
# The version that serves each network with a bundle, or Paris and Shanghai with version 2.
VERSION_OF = {"Paris": 2, "Shanghai": 2, "Cancun": 3, "Prague": 4, "Osaka": 5, "Amsterdam": 6}
VERSIONS = [
    (1, "Paris"),
    (2, "Paris"),
    (2, "Shanghai"),
    (3, "Cancun"),
    (4, "Prague"),
    (5, "Osaka"),
    (6, "Amsterdam"),
]

# The pinned block access list of an Amsterdam payload, which the stored header hashes.
ACCESS_LIST = bytes.fromhex(
    next(
        case["params"][0]["blockAccessList"]
        for case in _PAYLOADS
        if case["network"] == "Amsterdam" and "blockAccessList" in case["params"][0]
    ).removeprefix("0x")
)


def _kzg(case: str) -> tuple[bytes, bytes, bytes]:
    """The blob, commitment and proof of a pinned correct case of verify_blob_kzg_proof."""
    data = YAML(typ="safe").load(_KZG / f"verify_blob_kzg_proof_case_{case}" / "data.yaml")
    blob, commitment, proof = (
        bytes.fromhex(data["input"][key].removeprefix("0x"))
        for key in ("blob", "commitment", "proof")
    )
    return blob, commitment, proof


ZERO = _kzg("correct_proof_point_at_infinity_for_zero_poly")
FIRST = _kzg("correct_proof_0")
SECOND = _kzg("correct_proof_1")


def _versioned_hash(commitment: bytes) -> bytes:
    """The EIP-4844 versioned hash of a commitment, computed here with SHA-256."""
    return b"\x01" + hashlib.sha256(commitment).digest()[1:]


def _quantity(raw: bytes | int) -> str:
    """The Engine API quantity of a big-endian number or an integer."""
    return hex(raw if isinstance(raw, int) else int.from_bytes(raw, "big"))


def _data(raw: bytes) -> str:
    """The Engine API data of bytes."""
    return "0x" + raw.hex()


@functools.cache
def _built(network: str) -> tuple[bytes, bytes, tuple[bytes, ...], int]:
    """The block, accounts, requests and value that the build of the fixture's first block gives."""
    items = rlp.decode(bytes.fromhex(_first_block(network)["rlp"].removeprefix("0x")))
    header, transactions = items[0], items[1]
    withdrawals = items[3] if len(items) > 3 else None
    chain_config, state, recent = _chain(network)
    block, accounts, requests, value = engine.build_payload(
        chain_config,
        state,
        recent,
        METHODS[network],
        _attributes(header, withdrawals),
        fee_recipient=header[COINBASE],
        extra_data=header[EXTRA_DATA],
        target_gas_limit=int.from_bytes(header[GAS_LIMIT], "big"),
        transactions=[_payload_transaction(tx) for tx in transactions],
    )
    if network == "Amsterdam":
        # A build keeps only the hash of its access list, so the store pairs a pinned one with it.
        items = rlp.decode(block)
        items[0][BAL_HASH] = keccak256(ACCESS_LIST)
        block = rlp.encode(items)
    return block, accounts, tuple(requests), value


def _with_transactions(network: str, block: bytes, transactions: list[bytes]) -> bytes:
    """The block with its typed transactions replaced, and its header's transactions root."""
    items = rlp.decode(block)
    items[1] = transactions
    items[0][TRANSACTIONS_ROOT] = blocks.transactions_root(
        FORK_OF_NETWORK[network], rlp.encode(items)
    )
    return rlp.encode(items)


def _with_requests(block: bytes, requests: list[bytes]) -> bytes:
    """The block with its header's requests hash replaced by that of other requests."""
    items = rlp.decode(block)
    items[0][REQUESTS_HASH] = blocks.requests_hash(rlp.encode(requests))
    return rlp.encode(items)


def _entry(
    network: str,
    *,
    identifier: bytes = ID,
    fork: str | None = None,
    block: bytes | None = None,
    accounts: bytes | None = None,
    requests: list[bytes] | None = None,
    value: int | None = None,
    sidecars: list[bytes] | None = None,
    override: bool = False,
    access_list: bytes | None = None,
    no_access_list: bool = False,
) -> engine.PayloadEntry:
    """One snapshot entry from the build of a network, with chosen fields replaced."""
    built, built_accounts, built_requests, built_value = _built(network)
    if access_list is None and network == "Amsterdam" and not no_access_list:
        access_list = ACCESS_LIST
    return (
        identifier,
        FORK_OF_NETWORK[network] if fork is None else fork,
        built if block is None else block,
        built_accounts if accounts is None else accounts,
        list(built_requests) if requests is None else requests,
        built_value if value is None else value,
        sidecars or [],
        override,
        access_list,
    )


def _call(
    network: str, version: int, entries: list[engine.PayloadEntry], identifier: bytes = ID
) -> dict:
    """The answer to a call of a version, on the configuration of a network."""
    return engine.get_payload(
        config(network), entries, f"engine_getPayloadV{version}", ["0x" + identifier.hex()]
    )


def _payload_json(network: str, block: bytes) -> dict[str, object]:
    """The execution payload of a block, read here from its RLP fields."""
    items = rlp.decode(block)
    header = items[0]
    payload: dict[str, object] = {
        "parentHash": _data(header[0]),
        "feeRecipient": _data(header[2]),
        "stateRoot": _data(header[3]),
        "receiptsRoot": _data(header[5]),
        "logsBloom": _data(header[6]),
        "prevRandao": _data(header[13]),
        "blockNumber": _quantity(header[8]),
        "gasLimit": _quantity(header[9]),
        "gasUsed": _quantity(header[10]),
        "timestamp": _quantity(header[11]),
        "extraData": _data(header[12]),
        "baseFeePerGas": _quantity(header[15]),
        "blockHash": _data(keccak256(rlp.encode(header))),
        "transactions": [_data(_payload_transaction(tx)) for tx in items[1]],
    }
    if len(items) > 3:
        payload["withdrawals"] = [
            {
                "index": _quantity(index),
                "validatorIndex": _quantity(validator),
                "address": _data(address),
                "amount": _quantity(amount),
            }
            for index, validator, address, amount in items[3]
        ]
    if len(header) > 18:
        payload["blobGasUsed"] = _quantity(header[17])
        payload["excessBlobGas"] = _quantity(header[18])
    if network == "Amsterdam":
        payload["blockAccessList"] = _data(ACCESS_LIST)
        payload["slotNumber"] = _quantity(header[22])
    return payload


@pytest.mark.parametrize(("version", "network"), VERSIONS)
def test_version(version: int, network: str) -> None:
    """Each version returns exactly its fields, with the payload form of the built block."""
    block, _, requests, value = _built(network)
    result = _call(network, version, [_entry(network)])
    payload = _payload_json(network, block)
    if version == 1:
        assert result == payload
        return
    expected: dict[str, object] = {"executionPayload": payload, "blockValue": _quantity(value)}
    if version >= 3:
        expected |= {
            "blobsBundle": {"blobs": [], "commitments": [], "proofs": []},
            "shouldOverrideBuilder": False,
        }
    if version >= 4:
        expected["executionRequests"] = [_data(r) for r in requests]
    assert result == expected


@pytest.mark.parametrize(("version", "network"), VERSIONS[1:-1])
def test_block_hash_of_the_fixture(version: int, network: str) -> None:
    """The returned block hash is the hash of the fixture's block, which the build reproduces."""
    payload = _call(network, version, [_entry(network)])["executionPayload"]
    assert payload["blockHash"] == "0x" + _first_block(network)["hash"].removeprefix("0x")


@pytest.mark.parametrize(("version", "network"), VERSIONS)
def test_unknown_payload(version: int, network: str) -> None:
    """An ID with no build is -38001, before any other check."""
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.unknownPayload") as e:
        _call(network, version, [_entry(network)], UNKNOWN)
    assert e.value.code == 38001


@pytest.mark.parametrize(
    ("version", "network"),
    [
        (1, "Shanghai"),
        (2, "Cancun"),
        (3, "Shanghai"),
        (3, "Prague"),
        (4, "Cancun"),
        (4, "Osaka"),
        (5, "Prague"),
        (5, "Amsterdam"),
        (6, "Osaka"),
    ],
)
def test_unsupported_fork(version: int, network: str) -> None:
    """A build outside the forks of the version is -38005, at both ends of its range."""
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork") as e:
        _call(network, version, [_entry(network)])
    assert e.value.code == 38005


def _blob_transaction(hashes: list[bytes], nonce: int = 0) -> list:
    """The RLP fields of an unsigned type-3 transaction body with these versioned hashes."""
    return [
        b"\x01",
        nonce.to_bytes(1, "big") if nonce else b"",
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


def _network_form(
    network: str, body: list, blobs: list[bytes], commitments: list[bytes], proofs: list[bytes]
) -> bytes:
    """The network form of a blob transaction, with the wrapper version from Osaka."""
    version = [b"\x01"] if network in CELL_NETWORKS else []
    return b"\x03" + rlp.encode([body, *version, blobs, commitments, proofs])


def _bundle(network: str) -> tuple[bytes, list[bytes], dict[str, list[str]]]:
    """A block of two blob transactions with their network forms and the expected bundle."""
    if network in CELL_NETWORKS:
        # Cell proofs of the zero blob are all the point at infinity, so its pinned proof serves.
        pairs = [(ZERO, [ZERO[2]] * 128), (ZERO, [ZERO[2]] * 128)]
    else:
        pairs = [(FIRST, [FIRST[2]]), (SECOND, [SECOND[2]])]
    bodies = [
        _blob_transaction([_versioned_hash(blob[1])], nonce)
        for nonce, (blob, _) in enumerate(pairs)
    ]
    block = _with_transactions(
        network, _built(network)[0], [b"\x03" + rlp.encode(b) for b in bodies]
    )
    sidecars = [
        _network_form(network, body, [blob[0]], [blob[1]], proofs)
        for body, (blob, proofs) in zip(bodies, pairs, strict=True)
    ]
    expected = {
        "blobs": [_data(blob[0]) for blob, _ in pairs],
        "commitments": [_data(blob[1]) for blob, _ in pairs],
        "proofs": [_data(p) for _, proofs in pairs for p in proofs],
    }
    return block, sidecars, expected


@pytest.mark.parametrize(
    ("version", "network"), [(3, "Cancun"), (4, "Prague"), (5, "Osaka"), (6, "Amsterdam")]
)
def test_bundle(version: int, network: str) -> None:
    """A checked bundle joins the sidecars in block order: one proof per blob, or 128 from Osaka."""
    block, sidecars, expected = _bundle(network)
    entry = _entry(network, block=block, sidecars=sidecars, override=True)
    result = _call(network, version, [entry])
    assert result["blobsBundle"] == expected
    assert result["executionPayload"] == _payload_json(network, block)
    assert result["shouldOverrideBuilder"] is True


def _bundle_error(network: str, version: int, entry: engine.PayloadEntry, code: int) -> None:
    """Check that a stored bundle fails with a network error code, as malformed store data."""
    with raises(engine.EngineError, f"store: bundle error {code}") as e:
        _call(network, version, [entry])
    assert e.value.code == 0


def test_sidecars_out_of_order() -> None:
    """Sidecars in another order than the block's blob transactions fail the hash check."""
    block, sidecars, _ = _bundle("Cancun")
    _bundle_error("Cancun", 3, _entry("Cancun", block=block, sidecars=sidecars[::-1]), 103)


@pytest.mark.parametrize(("version", "network"), [(3, "Cancun"), (5, "Osaka")])
def test_missing_sidecar(version: int, network: str) -> None:
    """A blob transaction with no network form fails the count check."""
    block, sidecars, _ = _bundle(network)
    _bundle_error(network, version, _entry(network, block=block, sidecars=sidecars[:1]), 102)


def test_wrong_hash() -> None:
    """A commitment that does not hash to the block's versioned hash fails the hash check."""
    body = _blob_transaction([b"\x01" + b"\x00" * 31])
    block = _with_transactions("Cancun", _built("Cancun")[0], [b"\x03" + rlp.encode(body)])
    sidecar = _network_form("Cancun", body, [FIRST[0]], [FIRST[1]], [FIRST[2]])
    _bundle_error("Cancun", 3, _entry("Cancun", block=block, sidecars=[sidecar]), 103)


def _single(network: str, blob: bytes, proofs: list[bytes]) -> engine.PayloadEntry:
    """An entry whose one blob transaction commits to the zero commitment, with given contents."""
    body = _blob_transaction([_versioned_hash(ZERO[1])])
    block = _with_transactions(network, _built(network)[0], [b"\x03" + rlp.encode(body)])
    sidecar = _network_form(network, body, [blob], [ZERO[1]], proofs)
    return _entry(network, block=block, sidecars=[sidecar])


@pytest.mark.parametrize(("version", "network"), [(3, "Cancun"), (5, "Osaka")])
def test_proof_rejected(version: int, network: str) -> None:
    """Proofs that do not open the commitment to the blob fail the KZG check."""
    # Constant one has a nonzero commitment, so the zero commitment and proof cannot open it.
    blob = (b"\x00" * 31 + b"\x01") * 4096
    count = 128 if network in CELL_NETWORKS else 1
    _bundle_error(network, version, _single(network, blob, [ZERO[2]] * count), 105)


def test_invalid_kzg_input() -> None:
    """A blob with a field element at or above the modulus is not a KZG input."""
    blob = b"\xff" * 32 + ZERO[0][32:]
    _bundle_error("Cancun", 3, _single("Cancun", blob, [ZERO[2]]), 104)


@pytest.mark.parametrize(("network", "count"), [("Cancun", 2), ("Osaka", 127)])
def test_wrong_proof_count(network: str, count: int) -> None:
    """A bundle needs one proof per blob before Osaka, and 128 per blob from it."""
    version = 5 if network in CELL_NETWORKS else 3
    _bundle_error(network, version, _single(network, ZERO[0], [ZERO[2]] * count), 102)


def test_requests() -> None:
    """From Prague the stored execution requests are returned as they are."""
    requests = [b"\x00a", b"\x02b"]
    block = _with_requests(_built("Prague")[0], requests)
    result = _call("Prague", 4, [_entry("Prague", block=block, requests=requests)])
    assert result["executionRequests"] == ["0x0061", "0x0262"]
    assert result["executionPayload"] == _payload_json("Prague", block)


def test_requests_not_in_the_header() -> None:
    """Requests whose hash is not the header's do not give back the stored block."""
    with raises(engine.EngineError, "store: the payload does not give the block: error 403") as e:
        _call("Prague", 4, [_entry("Prague", requests=[b"\x00a"])])
    assert e.value.code == 0


def test_transactions_not_in_the_header() -> None:
    """Transactions that the header's root does not commit to do not give back the block."""
    items = rlp.decode(_built("Cancun")[0])
    items[1] = []
    with raises(engine.EngineError, "store: the payload does not give the block: error 403") as e:
        _call("Cancun", 3, [_entry("Cancun", block=rlp.encode(items))])
    assert e.value.code == 0


@pytest.mark.parametrize(
    ("network", "entry", "message"),
    [
        pytest.param(
            "Cancun",
            lambda: _entry("Cancun", fork="hegota"),
            "fork hegota not yet specified",
            id="unknown-fork",
        ),
        pytest.param(
            "Cancun",
            lambda: _entry("Cancun", value=2**256),
            "store: block value above 2^256",
            id="value",
        ),
        pytest.param(
            "Cancun",
            lambda: _entry("Cancun", requests=[b"\x00a"]),
            "store: execution requests out of order, too short or before Pectra",
            id="requests-before-prague",
        ),
        pytest.param(
            "Prague",
            lambda: _entry("Prague", requests=[b"\x01a", b"\x00b"]),
            "store: execution requests out of order, too short or before Pectra",
            id="requests-out-of-order",
        ),
        pytest.param(
            "Prague",
            lambda: _entry("Prague", requests=[b"\x00"]),
            "store: execution requests out of order, too short or before Pectra",
            id="request-too-short",
        ),
        pytest.param(
            "Prague",
            lambda: _entry("Cancun"),
            "store: the fork is not the configured fork at the block",
            id="wrong-fork",
        ),
        pytest.param(
            "Cancun",
            lambda: _entry("Cancun", access_list=ACCESS_LIST),
            "store: block access list: present before its fork",
            id="access-list-before-amsterdam",
        ),
        pytest.param(
            "Amsterdam",
            lambda: _entry("Amsterdam", no_access_list=True),
            "store: block access list: absent at its fork",
            id="no-access-list",
        ),
        pytest.param(
            "Amsterdam",
            lambda: _entry("Amsterdam", access_list=b"\xc0"),
            "store: the payload does not give the block: error 403",
            id="access-list-mismatch",
        ),
        pytest.param(
            "Cancun",
            lambda: _entry("Cancun", block=b"\xc1"),
            "store: block rejected: EthLib.Serialization.Rlp.RlpError.inputTooShort 1 0",
            id="block",
        ),
        pytest.param(
            "Cancun",
            lambda: _entry("Cancun", accounts=b"\xc1"),
            "store: state is not one RLP item",
            id="accounts",
        ),
        pytest.param(
            "Cancun",
            lambda: _entry("Cancun", sidecars=[b"\x02"]),
            "store: network error 2",
            id="network-form",
        ),
    ],
)
def test_malformed_store(
    network: str, entry: Callable[[], engine.PayloadEntry], message: str
) -> None:
    """Malformed snapshot data has code 0, since the export reads the store itself."""
    with raises(engine.EngineError, message) as e:
        _call(network, VERSION_OF[network], [entry()])
    assert e.value.code == 0


def test_duplicate_id() -> None:
    """A store holds each payload ID once."""
    entry = _entry("Paris")
    with raises(engine.EngineError, "store: two entries with one payload ID") as e:
        _call("Paris", 1, [entry, entry])
    assert e.value.code == 0


@pytest.mark.parametrize(
    ("params", "message"),
    [
        ([], 'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 1"'),
        (
            ["0x00"],
            'engine error: EthLib.Engine.EngineError.invalidParams "payloadId: 1 bytes, not 8"',
        ),
        (
            ["0x" + ID.hex(), "0x00"],
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 2, expected 1"',
        ),
    ],
)
def test_bad_params(params: list, message: str) -> None:
    """The request has exactly one parameter, an 8-byte payload ID; else -32602."""
    with raises(engine.EngineError, message) as e:
        engine.get_payload(config("Paris"), [], "engine_getPayloadV1", params)
    assert e.value.code == 32602


def test_unknown_method() -> None:
    """A method name past version 6 is not one of the method's versions."""
    with raises(engine.EngineError, "no method engine_getPayloadV7") as e:
        engine.get_payload(config("Paris"), [], "engine_getPayloadV7", [])
    assert e.value.code == 0
