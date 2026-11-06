"""The "eth" entry of a node record, against hand-built records."""

import pytest

from ethlib.errors import EnrError
from ethlib.networking import enr, forkid
from ethlib.serialization import rlp
from raising import raises

# The entry is `[[forkHash, forkNext], ...]`, from enr-entries/eth.md of ethereum/devp2p at the pin.
# No official vectors exist, so each record is RLP built here with a placeholder signature.
# The reader does not check the signature.

SIGNATURE = bytes(64)

# The mainnet identifier at Petersburg, from EIP-2124 "Test Cases".
FORK_HASH = bytes.fromhex("668db0af")
FORK_NEXT = 9_069_000
FORK_ID = [FORK_HASH, FORK_NEXT.to_bytes(3, "big")]


def _record(entries: dict[bytes, object]) -> bytes:
    pairs = sorted(entries.items())
    return rlp.encode([SIGNATURE, b"\x01"] + [x for pair in pairs for x in pair])


def test_entry() -> None:
    record = _record({b"eth": [FORK_ID], b"id": b"v4"})
    assert enr.eth_fork_id(record) == (FORK_HASH, FORK_NEXT)


def test_extra_elements_are_ignored() -> None:
    # A later version may add elements after the identifier.
    record = _record({b"eth": [FORK_ID, b"\x01", [b"future"]], b"id": b"v4"})
    assert enr.eth_fork_id(record) == (FORK_HASH, FORK_NEXT)


def test_no_entry() -> None:
    assert enr.eth_fork_id(_record({b"id": b"v4"})) is None


def test_entry_of_the_fork_id_export() -> None:
    # The identifier that a mainnet node computes reads back from its entry.
    fork_hash, fork_next = forkid.mainnet_fork_id(7_280_000, 0)
    entry = rlp.decode(forkid.encode(fork_hash, fork_next))
    assert enr.eth_fork_id(_record({b"eth": [entry], b"id": b"v4"})) == (fork_hash, fork_next)


@pytest.mark.parametrize(
    "value",
    [
        [],  # no identifier
        FORK_ID,  # the identifier itself, without the outer list
        b"\x01",  # a byte string
        [[FORK_HASH]],  # an identifier of one field
        [[FORK_HASH[:3], b""]],  # a hash of 3 bytes
        [[FORK_HASH, b"\x00"]],  # a next fork with a leading zero byte
    ],
)
def test_malformed_entry(value: object) -> None:
    with raises(EnrError, "eth entry is not a list that starts with [forkHash, forkNext]") as info:
        enr.eth_fork_id(_record({b"eth": value, b"id": b"v4"}))
    assert info.value.code == 0
