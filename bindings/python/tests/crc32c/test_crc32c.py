"""CRC-32C against the examples of RFC 3720 and the values of the CRC catalogue."""

import random

import pytest

from ethlib.cryptography import crc32c

# The SCSI Read (10) Command PDU of RFC 3720 Appendix B.4, four bytes per row as it prints them.
SCSI_READ_10 = bytes.fromhex(
    "01c00000"
    "00000000"
    "00000000"
    "00000000"
    "14000000"
    "00000400"
    "00000014"
    "00000018"
    "28000000"
    "00000000"
    "02000000"
    "00000000"
)

# The five examples of RFC 3720 Appendix B.4, with the digest bytes it prints.
# RFC 7143 Appendix A.4, which obsoletes RFC 3720, repeats them unchanged.
RFC3720_EXAMPLES = [
    (bytes(32), "aa36918a"),
    (b"\xff" * 32, "43aba862"),
    (bytes(range(32)), "4e79dd46"),
    (bytes(reversed(range(32))), "5cdb3f11"),
    (SCSI_READ_10, "563a96d9"),
]


@pytest.mark.parametrize("data, digest", RFC3720_EXAMPLES)
def test_rfc3720_examples(data: bytes, digest: str) -> None:
    assert crc32c.digest(data) == bytes.fromhex(digest)


def test_catalogue() -> None:
    # CRC-32/ISCSI of https://reveng.sourceforge.io/crc-catalogue/17plus.htm#crc.cat.crc-32-iscsi.
    # The empty message leaves the register at 0xffffffff, so the CRC is 0.
    assert crc32c.crc32c(b"") == 0
    # The check value: the nine ASCII bytes "123456789".
    assert crc32c.crc32c(b"123456789") == 0xE3069283


def reference(data: bytes) -> int:
    """CRC-32C bit by bit, with the reflected generator 0x82f63b78, independent of the Lean code."""
    crc = 0xFFFFFFFF
    for byte in data:
        crc ^= byte
        for _ in range(8):
            crc = (crc >> 1) ^ (0x82F63B78 if crc & 1 else 0)
    return crc ^ 0xFFFFFFFF


def test_reference() -> None:
    # Random messages of every length up to three 64-byte blocks, with a fixed seed.
    rng = random.Random(3720)
    for size in range(200):
        data = rng.randbytes(size)
        assert crc32c.crc32c(data) == reference(data)


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        crc32c.digest("abc")  # ty: ignore[invalid-argument-type]
