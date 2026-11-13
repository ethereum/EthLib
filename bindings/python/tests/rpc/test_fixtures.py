"""The requests of ethereum/execution-apis through the readers of the parameters."""

import hashlib
import json
from collections.abc import Sequence
from pathlib import Path

import pytest

from ethlib.execution import rpc
from raising import raises

# `fixtures/README.md` gives the origin of the files and their licence.
FIXTURES = Path(__file__).resolve().parent / "fixtures"

# The `eth_getProof` requests of the same commit, which the trie suite vendors.
# `trie/getproof/README.md` gives their origin and their licence.
GETPROOF = Path(__file__).resolve().parents[1] / "trie" / "getproof"

# The block hash that the balance and call fixtures name.
BLOCK_HASH = bytes.fromhex("6146b2fa7dd4d923ed43e2f25c8a2895369d15463ba974f83937f9a6fa58adbf")

# The hash of the head block, which the proof requests name.
HEAD_HASH = bytes.fromhex("52bccfc9c4d4874b1898c0fbd0ae3b598a0edc7b94d9b796857dbbe1093c32e0")


def exchange(path: Path) -> tuple[list[object], dict[str, object]]:
    """The parameters of the request of a fixture, and its response."""
    lines = path.read_text().splitlines()
    request = next(json.loads(line[3:]) for line in lines if line.startswith(">> "))
    response = next(json.loads(line[3:]) for line in lines if line.startswith("<< "))
    return request["params"], response


def test_digests() -> None:
    """Every file but the README and the pin list is pinned in `SHA256SUMS`, with its digest."""
    lines = (FIXTURES / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    entries = [line.split() for line in lines if line and not line.startswith("#")]
    assert all(len(entry) == 2 for entry in entries)
    names = (
        path.relative_to(FIXTURES).as_posix() for path in FIXTURES.rglob("*") if path.is_file()
    )
    vendored = set(names) - {"README.md", "SHA256SUMS"}
    assert sorted(name for _, name in entries) == sorted(vendored)
    for digest, name in entries:
        assert hashlib.sha256((FIXTURES / name).read_bytes()).hexdigest() == digest, name


# Each failing request, with the schemas of its parameters, the rejected index and the reason.
# The schemas are those of the methods in `src/debug/` and `src/eth/state.yaml` of the source.
# The source fixes only the code of an error, so the message of the fixture is never compared.
REJECTED = [
    pytest.param(
        "debug_getRawBlock/get-invalid-number.io",
        ["BlockNumberOrTag"],
        0,
        "BlockNumberOrTag: no 0x marker",
        id="getRawBlock-number",
    ),
    pytest.param(
        "debug_getRawHeader/get-invalid-number.io",
        ["BlockNumberOrTag"],
        0,
        "BlockNumberOrTag: no 0x marker",
        id="getRawHeader-number",
    ),
    pytest.param(
        "debug_getRawReceipts/get-invalid-number.io",
        ["BlockNumberOrTagOrHash"],
        0,
        "BlockNumberOrTagOrHash: not a block number, tag or hash",
        id="getRawReceipts-number",
    ),
    pytest.param(
        "debug_getRawTransaction/get-invalid-hash.io",
        ["hash32"],
        0,
        "hash32: no 0x marker",
        id="getRawTransaction-hash",
    ),
    # The request omits the optional second parameter, a TraceConfig.
    pytest.param(
        "debug_traceBlockByNumber/trace-block-invalid-number.io",
        ["BlockNumberOrTag"],
        0,
        "BlockNumberOrTag: no 0x marker",
        id="traceBlockByNumber-number",
    ),
    pytest.param(
        "eth_getStorageAt/get-storage-invalid-key.io",
        ["address", "bytesMax32", "BlockNumberOrTagOrHash"],
        1,
        "bytesMax32: not a hex digit",
        id="getStorageAt-key",
    ),
    pytest.param(
        "eth_getStorageAt/get-storage-invalid-key-too-large.io",
        ["address", "bytesMax32", "BlockNumberOrTagOrHash"],
        1,
        "bytesMax32: more than 64 hex digits",
        id="getStorageAt-key-65-digits",
    ),
]


@pytest.mark.parametrize(("name", "schemas", "rejected", "reason"), REJECTED)
def test_rejected_parameter(
    name: str, schemas: Sequence[rpc.Schema], rejected: int, reason: str
) -> None:
    """Every other parameter reads, and the rejected one raises the code of the fixture."""
    params, response = exchange(FIXTURES / name)
    assert len(params) == len(schemas)
    for index, (schema, value) in enumerate(zip(schemas, params, strict=True)):
        if index != rejected:
            rpc.read_param(schema, value)
    with raises(rpc.RpcError, reason) as error:
        rpc.read_param(schemas[rejected], params[rejected])
    fault = response["error"]
    assert isinstance(fault, dict)
    # The bindings carry a JSON-RPC code without its sign, as the Engine API exports do.
    assert error.value.code == -fault["code"]


# Each request whose block parameter is a tag, a hash, or an object of EIP-1898.
# Each schema is that of the parameter in `src/eth/state.yaml` or `src/eth/execute.yaml`.
BLOCKS = [
    pytest.param(
        FIXTURES / "eth_getBalance/get-balance-blockhash.io",
        1,
        ("hash", BLOCK_HASH, False),
        id="hash-string",
    ),
    pytest.param(
        FIXTURES / "eth_getBalance/get-balance-block-hash-object.io",
        1,
        ("hash", BLOCK_HASH, False),
        id="hash-object",
    ),
    pytest.param(
        FIXTURES / "eth_getBalance/get-balance-block-hash-object-require-canonical.io",
        1,
        ("hash", BLOCK_HASH, True),
        id="hash-object-canonical",
    ),
    pytest.param(
        FIXTURES / "eth_getBalance/get-balance-block-number-object.io",
        1,
        ("number", 50),
        id="number-object",
    ),
    pytest.param(
        FIXTURES / "eth_call/call-block-hash-object.io", 1, ("hash", BLOCK_HASH, False), id="call"
    ),
    pytest.param(
        GETPROOF / "get-account-proof-block-hash-object.io",
        2,
        ("hash", HEAD_HASH, False),
        id="getProof-hash-object",
    ),
    pytest.param(
        GETPROOF / "get-account-proof-blockhash.io",
        2,
        ("hash", HEAD_HASH, False),
        id="getProof-hash-string",
    ),
    pytest.param(
        GETPROOF / "get-account-proof-latest.io", 2, ("tag", "latest"), id="getProof-latest"
    ),
]


@pytest.mark.parametrize(("path", "index", "block"), BLOCKS)
def test_block_parameter(path: Path, index: int, block: rpc.BlockParam) -> None:
    """The block parameter of the request reads as the block that its JSON names."""
    params, _ = exchange(path)
    assert rpc.read_param("BlockNumberOrTagOrHash", params[index]) == block
