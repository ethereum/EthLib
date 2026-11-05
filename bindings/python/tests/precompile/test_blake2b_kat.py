"""BLAKE2b-512 of the BLAKE2 known answers, with the BLAKE2F precompile as compression function."""

import hashlib
import json
import struct
from pathlib import Path

import pytest

from ethlib.precompiles import run

from .test_blake2f import compress

ADDRESS = 0x09

# The precompile is the same at every fork from Istanbul, so the hash runs at the latest one.
FORK = "bpo2"

# The BLAKE2b entries of the BLAKE2 known answers.
#
# File: testvectors/blake2-kat.json
# Repository: BLAKE2/BLAKE2
# Commit: ed1974ea83433eba7b2d95c5dcd9ac33cb847913
# Licence: CC0 1.0 (blake2/COPYING)
KAT = Path(__file__).resolve().parent / "blake2" / "blake2b-kat.jsonl"

CASES = [json.loads(line) for line in KAT.read_text().splitlines()]

IV = [
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179,
]


def precompile(h: list[int], block: bytes, t: int, last: bool) -> list[int]:
    """F through the precompile, with the 12 rounds of BLAKE2b."""
    call = (
        struct.pack(">I", 12)
        + struct.pack("<8Q", *h)
        + block
        + struct.pack("<2Q", t, 0)
        + bytes([last])
    )
    return list(struct.unpack("<8Q", run(FORK, ADDRESS, call, 12)))


def oracle(h: list[int], block: bytes, t: int, last: bool) -> list[int]:
    """F through the Python oracle of the EIP-152 tests."""
    return compress(12, h, list(struct.unpack("<16Q", block)), t, 0, last)


def blake2b(data: bytes, key: bytes, f) -> bytes:
    """BLAKE2b-512 of RFC 7693 §3.3, with `f` as the compression function F."""
    # The parameter block of RFC 7693 §2.5: a 64-byte digest and the key length.
    h = [IV[0] ^ 0x01010000 ^ (len(key) << 8) ^ 64] + IV[1:]
    # A key is padded to one block and hashed before the data.
    message = (key.ljust(128, b"\0") if key else b"") + data
    blocks = [message[i : i + 128] for i in range(0, len(message), 128)] or [b""]
    for i, block in enumerate(blocks):
        last = i == len(blocks) - 1
        # The offset counter t counts the bytes hashed so far, this block included.
        t = min(len(message), 128 * (i + 1))
        h = f(h, block.ljust(128, b"\0"), t, last)
    return struct.pack("<8Q", *h)


def test_case_count() -> None:
    # 256 unkeyed and 256 keyed messages of 0 to 255 bytes; the keyed ones use a 64-byte key.
    assert [len(c["in"]) // 2 for c in CASES] == list(range(256)) * 2
    assert {c["hash"] for c in CASES} == {"blake2b"}
    assert [len(c["key"]) // 2 for c in CASES] == [0] * 256 + [64] * 256


def test_driver_with_oracle() -> None:
    # With the Python oracle as F, the driver meets the file too, so a failure below lies in the
    # precompile, not in the driver.
    # hashlib's BLAKE2b agrees with the file as well.
    for c in CASES[::17]:
        data, key = bytes.fromhex(c["in"]), bytes.fromhex(c["key"])
        assert blake2b(data, key, oracle) == bytes.fromhex(c["out"])
        assert hashlib.blake2b(data, key=key).digest() == bytes.fromhex(c["out"])


@pytest.mark.parametrize("case", CASES, ids=lambda c: f"{len(c['key']) // 2}-{len(c['in']) // 2}")
def test_kat(case: dict) -> None:
    data, key = bytes.fromhex(case["in"]), bytes.fromhex(case["key"])
    assert blake2b(data, key, precompile) == bytes.fromhex(case["out"])
