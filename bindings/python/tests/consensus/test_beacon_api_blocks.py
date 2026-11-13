"""The Beacon API answers that read one signed block, on the pinned static blocks."""

import copy
import hashlib
from functools import cache
from pathlib import Path
from typing import Any

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

STATIC = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "ssz_static" / "minimal"

SIGNATURE = "0x" + "c0" + "00" * 95

BLOB_BYTES = 4096 * 32


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


ALL = ["phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas"]


@pytest.mark.parametrize("fork", ALL)
def test_root_is_the_pinned_root(fork: str) -> None:
    root = YAML(typ="safe").load((_case(fork) / "roots.yaml").read_text())["root"]
    assert _query(fork, "root") == {"data": {"root": root}}


@pytest.mark.parametrize("fork", ALL)
def test_block_and_attestations(fork: str) -> None:
    signed = {"message": _message(fork), "signature": SIGNATURE}
    assert _query(fork, "block") == {"version": fork, "data": signed}
    attestations = _message(fork)["body"]["attestations"]
    assert _query(fork, "attestations") == {"version": fork, "data": attestations}


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


def test_no_blinded_block_from_gloas() -> None:
    with raises(consensus.ConsensusError, "Gloas blocks do not have a blinded form") as error:
        _query("gloas", "blinded_block")
    assert error.value.code == 400


def test_unknown_query() -> None:
    with raises(consensus.ConsensusError, "no block query is named header") as error:
        _query("deneb", "header")
    assert error.value.code == 0


def _commitment(i: int) -> bytes:
    return bytes([0xA0 + i]) * 48


def _blob(i: int) -> bytes:
    return bytes([i + 1]) * BLOB_BYTES


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
    hashes = [_versioned_hash(_commitment(i)) for i in (2, 0)]
    answer = consensus.api_blobs("minimal", FORKS[fork], block, blobs, hashes=hashes)
    assert answer == hex_of([0, 2])
    unknown = [_versioned_hash(_commitment(7))]
    assert consensus.api_blobs("minimal", FORKS[fork], block, blobs, hashes=unknown) == hex_of([])
    body = consensus.api_blobs_ssz("minimal", FORKS[fork], block, blobs, hashes=hashes)
    assert body == blobs[0] + blobs[2]


def test_no_blobs_before_deneb() -> None:
    block = _signed("capella")
    assert consensus.api_blobs("minimal", FORKS["capella"], block, []) == {"data": []}
    assert consensus.api_blobs_ssz("minimal", FORKS["capella"], block, []) == b""


def test_blobs_that_do_not_match_the_commitments() -> None:
    block = _with_commitments("deneb", 2)
    message = "Internal error: the blobs do not match the commitments of the block"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_blobs("minimal", FORKS["deneb"], block, [_blob(0)])
    assert error.value.code == 500
