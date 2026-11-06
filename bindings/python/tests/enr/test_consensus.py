"""The consensus entries of a node record, against hand-built records."""

from ethlib.networking import enr
from raising import raises

from .test_enr import _rlp_list

# Each record is RLP built here, with a placeholder signature, since the reader does not check it.
# Each value is written out by hand from its SSZ type.
# Each test names the rule that it pins.

SIGNATURE = bytes(64)

FORK_DIGEST = bytes.fromhex("6a95a1a9")
NEXT_VERSION = bytes.fromhex("06000000")
# ENRForkID: fork digest, next fork version, next fork epoch as a little-endian uint64.
# The epoch 2^64 - 1 says that no fork is planned.
ETH2 = FORK_DIGEST + NEXT_VERSION + b"\xff" * 8
# Bitvector[64] with bits 0 and 63 set: bit i is bit i % 8 of byte i // 8.
ATTNETS = bytes.fromhex("0100000000000080")
# Bitvector[4] with all four bits set.
SYNCNETS = bytes([0x0F])
# The custody group count 128, a big-endian integer with no leading zero byte.
CGC = bytes([0x80])
NFD = bytes.fromhex("aabbccdd")


def _record(entries: dict[bytes, bytes]) -> bytes:
    pairs = sorted(entries.items())
    return _rlp_list([SIGNATURE, b"\x01"] + [x for pair in pairs for x in pair])


FULL = {
    b"attnets": ATTNETS,
    b"cgc": CGC,
    b"eth2": ETH2,
    b"id": b"v4",
    b"nfd": NFD,
    b"syncnets": SYNCNETS,
}


def _without(key: bytes) -> dict[bytes, bytes]:
    return {k: v for k, v in FULL.items() if k != key}


def test_fulu_reads_every_entry():
    entries = enr.consensus_entries("fusaka", _record(FULL))
    assert entries.eth2 == enr.EnrForkId(FORK_DIGEST, NEXT_VERSION, 2**64 - 1)
    assert entries.attnets == ATTNETS
    assert entries.syncnets == SYNCNETS
    assert entries.cgc == 128
    assert entries.nfd == NFD


def test_phase0_ignores_later_entries():
    entries = enr.consensus_entries("phase0", _record(FULL))
    assert entries.attnets == ATTNETS
    assert (entries.syncnets, entries.cgc, entries.nfd) == (None, None, None)


def test_altair_reads_syncnets_only():
    entries = enr.consensus_entries("altair", _record(FULL))
    assert entries.syncnets == SYNCNETS
    assert (entries.cgc, entries.nfd) == (None, None)


def test_bpo2_is_after_fulu():
    entries = enr.consensus_entries("bpo2", _record(FULL))
    assert entries.cgc == 128


def test_attnets_may_be_absent():
    entries = enr.consensus_entries("fusaka", _record(_without(b"attnets")))
    assert entries.attnets is None


def test_missing_eth2():
    with raises(ValueError, "record has no eth2 entry"):
        enr.consensus_entries("phase0", _record(_without(b"eth2")))


def test_fulu_requires_cgc():
    with raises(ValueError, "record has no cgc entry"):
        enr.consensus_entries("fusaka", _record(_without(b"cgc")))


def test_fulu_requires_nfd():
    with raises(ValueError, "record has no nfd entry"):
        enr.consensus_entries("fusaka", _record(_without(b"nfd")))


def test_cgc_not_required_before_fulu():
    entries = enr.consensus_entries("pectra", _record(_without(b"cgc")))
    assert entries.cgc is None


def test_eth2_of_15_bytes():
    record = _record({**FULL, b"eth2": ETH2[:15]})
    with raises(ValueError, "the eth2 entry is not valid SSZ"):
        enr.consensus_entries("phase0", record)


def test_syncnets_bit_past_the_length():
    # Bit 4 of a Bitvector[4] must be zero.
    record = _record({**FULL, b"syncnets": bytes([0x10])})
    with raises(ValueError, "the syncnets entry is not valid SSZ"):
        enr.consensus_entries("altair", record)


def test_cgc_zero_is_empty():
    entries = enr.consensus_entries("fusaka", _record({**FULL, b"cgc": b""}))
    assert entries.cgc == 0


def test_cgc_leading_zero():
    record = _record({**FULL, b"cgc": bytes([0x00, 0x80])})
    with raises(
        ValueError, "the cgc entry is not a big-endian integer below 2^64 without leading zeros"
    ):
        enr.consensus_entries("fusaka", record)


def test_minimal_configuration():
    # The minimal configuration also has 64 attestation subnets.
    entries = enr.consensus_entries("fusaka", _record(FULL), config="minimal")
    assert entries.attnets == ATTNETS


def test_attnets_of_7_bytes():
    # 64 subnets need 8 bytes, so 7 bytes are rejected.
    record = _record({**FULL, b"attnets": ATTNETS[:7]})
    with raises(ValueError, "the attnets entry is not valid SSZ"):
        enr.consensus_entries("fusaka", record)
