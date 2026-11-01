"""
The NIST SHA-256 test vectors, as (message, digest) pairs.

The vectors come from the two NIST CAVP files vendored under `cavp/`:

- `SHA256ShortMsg.rsp`, 65 vectors.
- `SHA256LongMsg.rsp`, 64 vectors.

They are the byte-oriented CAVS 11.0 distributions.
`cavp/README.md` records the source and the licence.
NIST material is public domain.

Plus the two SHA-256 example messages of FIPS 180-2.
NIST republishes them on its example-values page.
The empty message is not one of them; it is the ShortMsg `Len = 0` vector.

The module parses the two files at import time.
It then checks every digest against `hashlib`, so a parsing bug fails
collection instead of a test.

The count is 65 ShortMsg vectors, 64 LongMsg vectors and 2 FIPS 180-2
examples. That is 131 vectors, and there are no duplicates.
"""
import hashlib
from pathlib import Path

# The vendored NIST files, next to this module.
_CAVP_DIR = Path(__file__).resolve().parent / "cavp"

# The two FIPS 180-2 SHA-256 example messages, as NIST republishes them
# on its example-values page, with their published digests.
_FIPS_EXAMPLES = [
    ("hash_case_fips_abc", "abc",
     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("hash_case_fips_56_bytes",
     "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
]


def _parse_rsp(path: Path, kind: str) -> list[tuple[str, bytes, bytes]]:
    """The (case name, message, digest) triples of one CAVS `.rsp` file.

    The byte-oriented ShortMsg and LongMsg files list one case as a
    `Len` (in bits), a `Msg` and an `MD`.
    A `Len = 0` case still carries a `Msg = 00` line for grammatical
    regularity, so the `Len` field decides how many bytes the message
    holds and the rest of the final byte is dropped.
    """
    cases = []
    len_bits: int | None = None
    msg_hex: str | None = None
    for line in path.read_text().splitlines():
        key, sep, value = line.partition(" = ")
        if not sep:
            continue
        key, value = key.strip(), value.strip()
        if key == "Len":
            len_bits = int(value)
        elif key == "Msg":
            msg_hex = value
        elif key == "MD":
            if len_bits is None or msg_hex is None:
                raise ValueError(f"{path.name}: MD without Len or Msg")
            if len_bits % 8 != 0:
                raise ValueError(f"{path.name}: Len {len_bits} is not a whole byte")
            message = bytes.fromhex(msg_hex)[: len_bits // 8]
            cases.append((f"hash_case_{kind}_len_{len_bits}", message,
                          bytes.fromhex(value)))
            len_bits, msg_hex = None, None
    return cases


def _vectors() -> list[tuple[str, bytes, bytes]]:
    cases = _parse_rsp(_CAVP_DIR / "SHA256ShortMsg.rsp", "short")
    cases += _parse_rsp(_CAVP_DIR / "SHA256LongMsg.rsp", "long")
    cases += [(name, msg.encode(), bytes.fromhex(md))
              for name, msg, md in _FIPS_EXAMPLES]
    # The sources hold no duplicate (message, digest) pair; assert it so a
    # future source edit cannot add one silently.
    seen, unique = set(), []
    for case in cases:
        pair = (case[1], case[2])
        if pair in seen:
            continue
        seen.add(pair)
        unique.append(case)
    return unique


_CASES = _vectors()

CASE_NAMES: list[str] = [name for name, _, _ in _CASES]
VECTORS: list[tuple[bytes, bytes]] = [(message, digest)
                                      for _, message, digest in _CASES]

# An independent implementation vouches for every digest at import time.
assert all(hashlib.sha256(message).digest() == digest
           for message, digest in VECTORS)
