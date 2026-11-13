"""The Beacon API answers that read signed blocks and their data, on pinned vectors."""

import copy
import hashlib
from functools import cache
from pathlib import Path
from typing import Any

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.cryptography.kzg import BYTES_PER_BLOB
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_fork_choice import _hex, _inputs, _load, _read

STATIC = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "ssz_static" / "minimal"

SIGNATURE = "0x" + "c0" + "00" * 95


def _case(fork: str) -> Path:
    return STATIC / fork / "ssz_static" / "BeaconBlock" / "ssz_random" / "case_0"


@cache
def _message(fork: str) -> dict[str, Any]:
    """The JSON of the pinned random block of a fork."""
    data = snappy.decompress((_case(fork) / "serialized.ssz_snappy").read_bytes())
    return consensus.api_json("minimal", FORKS[fork], "BeaconBlock", data)


def _signed(fork: str, message: dict[str, Any] | None = None) -> bytes:
    """The SSZ bytes of the pinned block of a fork, or of another message, with a signature."""
    signed = {"message": _message(fork) if message is None else message, "signature": SIGNATURE}
    return consensus.api_ssz("minimal", FORKS[fork], "SignedBeaconBlock", signed)


def _query(fork: str, query: str) -> dict[str, Any]:
    return consensus.api_block_query("minimal", FORKS[fork], _signed(fork), query)


ALL = ["phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"]


def _version(fork: str) -> dict[str, str]:
    """The version key of a versioned answer; the source names no version for Heze yet."""
    return {} if fork == "heze" else {"version": fork}


@pytest.mark.parametrize("fork", ALL)
def test_root_is_the_pinned_root(fork: str) -> None:
    root = YAML(typ="safe").load((_case(fork) / "roots.yaml").read_text())["root"]
    assert _query(fork, "root") == {"data": {"root": root}}


@pytest.mark.parametrize("fork", ALL)
def test_block_and_attestations(fork: str) -> None:
    signed = {"message": _message(fork), "signature": SIGNATURE}
    assert _query(fork, "block") == {**_version(fork), "data": signed}
    attestations = _message(fork)["body"]["attestations"]
    assert _query(fork, "attestations") == {**_version(fork), "data": attestations}


@pytest.mark.parametrize("fork", ["phase0", "altair"])
def test_blinded_block_before_bellatrix_is_the_block(fork: str) -> None:
    assert _query(fork, "blinded_block") == _query(fork, "block")


@pytest.mark.parametrize("fork", ["bellatrix", "capella", "deneb", "electra", "fulu"])
def test_blinded_block_holds_the_header_of_the_payload(fork: str) -> None:
    answer = _query(fork, "blinded_block")
    assert answer["version"] == fork
    assert answer["data"]["signature"] == SIGNATURE
    blinded = answer["data"]["message"]
    message = _message(fork)
    assert {k: v for k, v in blinded.items() if k != "body"} == {
        k: v for k, v in message.items() if k != "body"
    }
    payload = message["body"]["execution_payload"]
    header = blinded["body"]["execution_payload_header"]
    # The header copies every field of the payload but its lists, which become roots.
    for key, value in payload.items():
        if key in ("transactions", "withdrawals"):
            assert f"{key}_root" in header
        else:
            assert header[key] == value
    rest = {k: v for k, v in message["body"].items() if k != "execution_payload"}
    assert {k: v for k, v in blinded["body"].items() if k != "execution_payload_header"} == rest
    # The blinded block has the pinned root of its block, so every root of the header is right.
    encoded = consensus.api_ssz("minimal", FORKS[fork], "BlindedBeaconBlock", blinded)
    root, _ = consensus.ssz_static("minimal", FORKS[fork], "BlindedBeaconBlock", encoded)
    pinned = YAML(typ="safe").load((_case(fork) / "roots.yaml").read_text())["root"]
    assert "0x" + root.hex() == pinned


@pytest.mark.parametrize("fork", ["gloas", "heze"])
def test_no_blinded_block_from_gloas(fork: str) -> None:
    message = "Blocks from Gloas on do not have a blinded form"
    with raises(consensus.ConsensusError, message) as error:
        _query(fork, "blinded_block")
    assert error.value.code == 400


def test_unknown_query() -> None:
    with raises(consensus.ConsensusError, "no block query is named header") as error:
        _query("deneb", "header")
    assert error.value.code == 0


def _commitment(i: int) -> bytes:
    return bytes([0xA0 + i]) * 48


def _blob(i: int) -> bytes:
    return bytes([i + 1]) * BYTES_PER_BLOB


def _versioned_hash(commitment: bytes) -> bytes:
    """The KZG version byte, then the last 31 bytes of the SHA-256 hash of the commitment."""
    return b"\x01" + hashlib.sha256(commitment).digest()[1:]


def _with_commitments(fork: str, count: int) -> bytes:
    """The pinned block of a fork, committing to the first commitments above."""
    message = copy.deepcopy(_message(fork))
    commitments = ["0x" + _commitment(i).hex() for i in range(count)]
    if fork == "gloas":
        bid = message["body"]["signed_execution_payload_bid"]["message"]
        bid["blob_kzg_commitments"] = commitments
    else:
        message["body"]["blob_kzg_commitments"] = commitments
    return _signed(fork, message)


@pytest.mark.parametrize("fork", ["deneb", "fulu", "gloas"])
def test_blobs_in_the_order_of_the_commitments(fork: str) -> None:
    block = _with_commitments(fork, 3)
    blobs = [_blob(i) for i in range(3)]

    def hex_of(indices: list[int]) -> dict[str, Any]:
        return {"data": ["0x" + blobs[i].hex() for i in indices]}

    assert consensus.api_blobs("minimal", FORKS[fork], block, blobs) == hex_of([0, 1, 2])
    # The answer keeps the order of the block, whatever the order of the hashes.
    hashes = [_versioned_hash(_commitment(i)) for i in (2, 1)]
    answer = consensus.api_blobs("minimal", FORKS[fork], block, blobs, hashes=hashes)
    assert answer == hex_of([1, 2])
    unknown = [_versioned_hash(_commitment(7))]
    assert consensus.api_blobs("minimal", FORKS[fork], block, blobs, hashes=unknown) == hex_of([])
    body = consensus.api_blobs_ssz("minimal", FORKS[fork], block, blobs, hashes=hashes)
    assert body == blobs[1] + blobs[2]
    # An empty list of hashes is a request for no blob.
    assert consensus.api_blobs("minimal", FORKS[fork], block, blobs, hashes=[]) == hex_of([])


def test_no_blobs_before_deneb() -> None:
    block = _signed("capella")
    assert consensus.api_blobs("minimal", FORKS["capella"], block, []) == {"data": []}
    assert consensus.api_blobs_ssz("minimal", FORKS["capella"], block, []) == b""


@pytest.mark.parametrize("count", [1, 3])
def test_blobs_that_do_not_match_the_commitments(count: int) -> None:
    block = _with_commitments("deneb", 2)
    blobs = [_blob(i) for i in range(count)]
    message = "Internal error: the blobs do not match the commitments of the block"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_blobs("minimal", FORKS["deneb"], block, blobs)
    assert error.value.code == 500
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_blobs_ssz("minimal", FORKS["deneb"], block, blobs)
    assert error.value.code == 500


@pytest.mark.parametrize("fork", ALL)
def test_block_ssz_is_the_signed_block(fork: str) -> None:
    body = consensus.api_block_query_ssz("minimal", FORKS[fork], _signed(fork), "block")
    assert body == _signed(fork)


@pytest.mark.parametrize("fork", ["phase0", "bellatrix", "fulu"])
def test_blinded_block_ssz_encodes_the_json_answer(fork: str) -> None:
    kind = "SignedBeaconBlock" if fork == "phase0" else "SignedBlindedBeaconBlock"
    document = _query(fork, "blinded_block")["data"]
    encoded = consensus.api_ssz("minimal", FORKS[fork], kind, document)
    body = consensus.api_block_query_ssz("minimal", FORKS[fork], _signed(fork), "blinded_block")
    assert body == encoded


@pytest.mark.parametrize("fork", ["gloas", "heze"])
def test_no_blinded_block_ssz_from_gloas(fork: str) -> None:
    message = "Blocks from Gloas on do not have a blinded form"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_block_query_ssz("minimal", FORKS[fork], _signed(fork), "blinded_block")
    assert error.value.code == 400


def test_attestations_have_no_ssz_body() -> None:
    message = "no block query with an SSZ body is named attestations"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_block_query_ssz("minimal", FORKS["deneb"], _signed("deneb"), "attestations")
    assert error.value.code == 0


GLOAS_CASES = Path(__file__).resolve().parents[4] / "tests/consensus/fork_choice/minimal/gloas"
# A block at slot 1 on the anchor, then the envelope of its payload.
ENVELOPE_CASE = (
    GLOAS_CASES
    / "fork_choice/on_execution_payload_envelope/pyspec_tests/on_execution_payload_envelope_valid"
)
# The same block at slot 1, then two children of it: the head at slot 3, and a block at slot 2.
FORK_CASE = GLOAS_CASES / "fork_choice/ex_ante/pyspec_tests/ex_ante_vanilla"
HEAD_ROOT = "0x551ef523e59e967a78834e3e80fd3b71008e42b57ba768cfdc2ba43cec47b28a"
SIDE_ROOT = "0x9a319e277bcad69ccdc06f393d93d54407fd6f7a414c2f6ae73c4432d1ebfc21"
ANCHOR_ROOT = "0xde6ee16691ac31262a6bb5552e4854c07abb7a9ac8539c616ba4ed4e9aaa1adc"
BLOCK_ROOT = "0x29874e204fad82a30293db7910390d39dc70d4e7c5a7302cfbc10a1b8f17dcf4"
ENVELOPE = (
    "execution_payload_envelope_0x131ab93ae0a85b4dae8dd199874c24c136c7c8645f3a7b21bb0135cff179e47a"
)
GLOAS = FORKS["gloas"]


@cache
def _store_case(
    case: Path = ENVELOPE_CASE,
) -> tuple[str, str, bytes, bytes, list[consensus.ForkChoiceStep]]:
    """The arguments that build the store after every step of a Gloas fork choice case."""
    steps = [step for raw in _load(case / "steps.yaml") for step in _inputs(case, raw)]
    return "minimal", GLOAS, _read(case, "anchor_state"), _read(case, "anchor_block"), steps


def _block_bytes() -> bytes:
    return _read(ENVELOPE_CASE, f"block_{BLOCK_ROOT}")


def _anchor_signed() -> bytes:
    """The anchor block of the case, with a signature."""
    anchor_block = _read(ENVELOPE_CASE, "anchor_block")
    anchor = consensus.api_json("minimal", GLOAS, "BeaconBlock", anchor_block)
    signed = {"message": anchor, "signature": SIGNATURE}
    return consensus.api_ssz("minimal", GLOAS, "SignedBeaconBlock", signed)


def _header(signed: bytes) -> tuple[bytes, dict[str, Any]]:
    """The SSZ and the JSON of the signed header of a signed block."""
    block = consensus.api_json("minimal", GLOAS, "SignedBeaconBlock", signed)
    message = block["message"]
    body = consensus.api_ssz("minimal", GLOAS, "BeaconBlockBody", message["body"])
    body_root, _ = consensus.ssz_static("minimal", GLOAS, "BeaconBlockBody", body)
    fields = ("slot", "proposer_index", "parent_root", "state_root")
    header = {
        "message": {**{key: message[key] for key in fields}, "body_root": "0x" + body_root.hex()},
        "signature": block["signature"],
    }
    return consensus.api_ssz("minimal", GLOAS, "SignedBeaconBlockHeader", header), header


def test_header_of_the_head_is_canonical() -> None:
    answer = consensus.api_header(*_store_case(), _block_bytes())
    _, header = _header(_block_bytes())
    assert answer == {"data": {"root": BLOCK_ROOT, "canonical": True, "header": header}}


def test_header_of_the_anchor_is_canonical() -> None:
    answer = consensus.api_header(*_store_case(), _anchor_signed())
    _, header = _header(_anchor_signed())
    assert answer == {"data": {"root": ANCHOR_ROOT, "canonical": True, "header": header}}


def test_header_of_an_unknown_block_is_not_canonical() -> None:
    answer = consensus.api_header(*_store_case(), _signed("gloas"))
    root = YAML(typ="safe").load((_case("gloas") / "roots.yaml").read_text())["root"]
    _, header = _header(_signed("gloas"))
    assert answer == {"data": {"root": root, "canonical": False, "header": header}}


def test_headers_of_two_children() -> None:
    head, head_json = _header(_read(FORK_CASE, f"block_{HEAD_ROOT}"))
    side, side_json = _header(_read(FORK_CASE, f"block_{SIDE_ROOT}"))
    # Both children have the block at slot 1 as parent, and neither is at that slot.
    # The answer keeps the order of the input, and only the head is on the chain of the head.
    held = [head, side]
    answer = consensus.api_headers(*_store_case(FORK_CASE), held, parent_root=_hex(BLOCK_ROOT))
    assert answer["data"] == [
        {"root": HEAD_ROOT, "canonical": True, "header": head_json},
        {"root": SIDE_ROOT, "canonical": False, "header": side_json},
    ]
    reversed_answer = consensus.api_headers(
        *_store_case(FORK_CASE), held[::-1], parent_root=_hex(BLOCK_ROOT)
    )
    assert reversed_answer["data"] == answer["data"][::-1]


def test_headers_filters() -> None:
    block, block_json = _header(_block_bytes())
    anchor, anchor_json = _header(_anchor_signed())

    def headers(**filters: Any) -> list[dict[str, Any]]:
        return consensus.api_headers(*_store_case(), [anchor, block], **filters)["data"]

    on_block = {"root": BLOCK_ROOT, "canonical": True, "header": block_json}
    on_anchor = {"root": ANCHOR_ROOT, "canonical": True, "header": anchor_json}
    # With no filter, the headers at the slot of the head, which is slot 1.
    assert headers() == [on_block]
    assert headers(slot=0) == [on_anchor]
    assert headers(parent_root=_hex(ANCHOR_ROOT)) == [on_block]
    # The anchor has the zero parent root, at slot 0 rather than the slot of the head.
    assert headers(parent_root=bytes(32)) == [on_anchor]
    assert headers(slot=0, parent_root=_hex(ANCHOR_ROOT)) == []
    assert headers(slot=5) == []


def test_payload_envelope_of_the_block() -> None:
    signed = _read(ENVELOPE_CASE, ENVELOPE)
    answer = consensus.api_payload_envelope(*_store_case(), _hex(BLOCK_ROOT), signed)
    document = consensus.api_json("minimal", GLOAS, "SignedExecutionPayloadEnvelope", signed)
    assert answer == {"version": "gloas", "data": document}
    body = consensus.api_payload_envelope_ssz(*_store_case(), _hex(BLOCK_ROOT), signed)
    assert body == signed


def test_payload_envelope_not_held() -> None:
    signed = _read(ENVELOPE_CASE, ENVELOPE)
    document = consensus.api_json("minimal", GLOAS, "SignedExecutionPayloadEnvelope", signed)
    builder = int(document["message"]["builder_index"])
    document["message"]["builder_index"] = str((builder + 1) % 2**64)
    other = consensus.api_ssz("minimal", GLOAS, "SignedExecutionPayloadEnvelope", document)
    # The anchor has no envelope, and another message is not the one that the store holds.
    for root, envelope in [(ANCHOR_ROOT, signed), (BLOCK_ROOT, other)]:
        with raises(consensus.ForkChoiceError, "Execution payload envelope not found") as error:
            consensus.api_payload_envelope(*_store_case(), _hex(root), envelope)
        assert error.value.code == 404


def _sidecar(fork: str, index: int) -> bytes:
    """The SSZ of the pinned random sidecar of a fork, at another index."""
    case = STATIC / fork / "ssz_static" / "DataColumnSidecar" / "ssz_random" / "case_0"
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    document = consensus.api_json("minimal", FORKS[fork], "DataColumnSidecar", data)
    document["index"] = str(index)
    return consensus.api_ssz("minimal", FORKS[fork], "DataColumnSidecar", document)


@pytest.mark.parametrize("fork", ["fulu", "gloas"])
def test_columns_with_the_requested_indices(fork: str) -> None:
    held = [_sidecar(fork, i) for i in (5, 2, 9)]

    def documents(indices: list[int]) -> list[dict[str, Any]]:
        return [
            consensus.api_json("minimal", FORKS[fork], "DataColumnSidecar", _sidecar(fork, i))
            for i in indices
        ]

    answer = consensus.api_columns("minimal", FORKS[fork], held)
    assert answer == {"version": fork, "data": documents([5, 2, 9])}
    # The source allows any order; EthLib keeps the order of the input.
    chosen = consensus.api_columns("minimal", FORKS[fork], held, indices=[9, 2, 4])
    assert chosen["data"] == documents([2, 9])
    assert consensus.api_columns("minimal", FORKS[fork], held, indices=[])["data"] == []
    # A list of variable-size sidecars: one four-byte offset each, then the sidecars.
    body = consensus.api_columns_ssz("minimal", FORKS[fork], held, indices=[2, 9])
    first, second = _sidecar(fork, 2), _sidecar(fork, 9)
    offsets = (8).to_bytes(4, "little") + (8 + len(first)).to_bytes(4, "little")
    assert body == offsets + first + second
    assert consensus.api_columns_ssz("minimal", FORKS[fork], held, indices=[]) == b""


def test_no_columns_before_fulu() -> None:
    message = "Blocks before Fulu do not have data column sidecars"
    for answer in (consensus.api_columns, consensus.api_columns_ssz):
        with raises(consensus.ConsensusError, message) as error:
            answer("minimal", FORKS["electra"], [])
        assert error.value.code == 400
