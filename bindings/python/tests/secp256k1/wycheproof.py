"""
Readers for the Wycheproof ECDSA test sets of secp256k1.

The sets come from `C2SP/wycheproof` at commit
d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9, in `testvectors_v1/`.
They keep their licence, the Apache License 2.0, in `wycheproof/LICENSE`.

Each test signs a message hashed with SHA-256.
The hash is Python's `hashlib.sha256`: SHA-256 is not under test here.
"""

import hashlib
import json
from pathlib import Path

DIR = Path(__file__).resolve().parent / "wycheproof"

P1363 = "ecdsa_secp256k1_sha256_p1363_test.json"
BITCOIN = "ecdsa_secp256k1_sha256_bitcoin_test.json"


def cases(name: str):
    """Each test of a set, as (tcId, public key, hash, signature, valid)."""
    data = json.loads((DIR / name).read_text())
    for group in data["testGroups"]:
        # The key is the 65-byte SEC 1 uncompressed encoding.
        public_key = bytes.fromhex(group["publicKey"]["uncompressed"])
        for test in group["tests"]:
            # These sets have no "acceptable" result, only valid and invalid.
            assert test["result"] in ("valid", "invalid")
            msg_hash = hashlib.sha256(bytes.fromhex(test["msg"])).digest()
            yield (test["tcId"], public_key, msg_hash, bytes.fromhex(test["sig"]),
                   test["result"] == "valid")


def der_signature(der: bytes) -> bytes | None:
    """The 64-byte `r || s` of a strict DER signature, or None.

    The Bitcoin set encodes signatures in DER, as `SEQUENCE { INTEGER r, INTEGER s }`.
    DER allows one encoding per value, so this reader rejects every other:

    - a long-form length, which DER forbids below 128;
    - an integer with a needless leading zero byte, or a negative one;
    - trailing bytes, or a length that overruns the input.

    An integer that needs more than 32 bytes is also None: it cannot be below `n`.
    """
    def length(buf: bytes, at: int) -> tuple[int, int] | None:
        # Every length here is below 128, so it takes the short form.
        if at >= len(buf) or buf[at] >= 0x80:
            return None
        return buf[at], at + 1

    def integer(buf: bytes, at: int) -> tuple[int, int] | None:
        if at >= len(buf) or buf[at] != 0x02:
            return None
        got = length(buf, at + 1)
        if got is None:
            return None
        size, at = got
        body = buf[at:at + size]
        if size == 0 or len(body) != size:
            return None
        # Negative, or a zero byte the next byte does not need.
        if body[0] >= 0x80 or (size > 1 and body[0] == 0 and body[1] < 0x80):
            return None
        return int.from_bytes(body, "big"), at + size

    if len(der) < 2 or der[0] != 0x30:
        return None
    got = length(der, 1)
    if got is None or got[0] != len(der) - got[1]:
        return None
    first = integer(der, got[1])
    if first is None:
        return None
    second = integer(der, first[1])
    if second is None or second[1] != len(der):
        return None
    r, s = first[0], second[0]
    if r >= 1 << 256 or s >= 1 << 256:
        return None
    return r.to_bytes(32, "big") + s.to_bytes(32, "big")
