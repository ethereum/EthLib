"""The status of a Builder API request that submits a signed blinded block."""

import struct
from pathlib import Path

import pytest

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy
from raising import raises

# A valid Bellatrix block of the sanity vectors, on its state before it.
CASE = (
    Path(__file__).resolve().parents[4]
    / "tests"
    / "consensus"
    / "transition"
    / "minimal"
    / "bellatrix"
    / "sanity"
    / "blocks"
    / "pyspec_tests"
    / "attestation"
)

# The fixed part of a Bellatrix body before the offset of its payload, in the minimal preset.
# It holds the RANDAO reveal, the eth1 data, the graffiti, five offsets and the sync aggregate.
PAYLOAD_OFFSET_AT = 96 + 72 + 32 + 5 * 4 + (4 + 96)


def _read(name: str) -> bytes:
    return snappy.decompress((CASE / name).read_bytes())


def _payload(signed: bytes) -> bytes:
    """The execution payload of a signed Bellatrix block, the last field of its body."""
    # A signed block is the offset of its message and its signature, then the message.
    # The message holds the slot, the proposer, two roots and the offset of its body.
    body = signed[100 + 84 :]
    (offset,) = struct.unpack_from("<I", body, PAYLOAD_OFFSET_AT)
    return body[offset:]


STATE = _read("pre.ssz_snappy")
BLOCK = _read("blocks_0.ssz_snappy")
BLINDED = consensus.api_block_query_ssz("minimal", "bellatrix", BLOCK, "blinded_block")
PAYLOAD = _payload(BLOCK)


def _status(blinded: bytes, payload: bytes, version: str) -> int:
    return consensus.submit_blinded_block_status(
        "minimal", "bellatrix", STATE, blinded, payload, version
    )


@pytest.mark.parametrize(("version", "status"), [("v1", 200), ("v2", 202)])
def test_valid_block(version: str, status: int) -> None:
    """A block that unblinds with the payload and passes the transition gets the success."""
    assert _status(BLINDED, PAYLOAD, version) == status


@pytest.mark.parametrize("version", ["v1", "v2"])
def test_bad_signature(version: str) -> None:
    """A changed byte of the signature fails the proposer check of the transition."""
    blinded = bytearray(BLINDED)
    blinded[4] ^= 1
    assert _status(bytes(blinded), PAYLOAD, version) == 400


@pytest.mark.parametrize("version", ["v1", "v2"])
def test_other_payload(version: str) -> None:
    """A payload with another fee recipient has another header, so the block does not unblind."""
    payload = bytearray(PAYLOAD)
    payload[32] ^= 1
    assert _status(BLINDED, bytes(payload), version) == 400


def test_unknown_version() -> None:
    """Only the two endpoints have a status."""
    with raises(SszError, "no endpoint version v3") as error:
        _status(BLINDED, PAYLOAD, "v3")
    assert error.value.code == 0
