"""
The NIST SHA-256 test vectors, as (message, digest) pairs.

- 65 vectors from `cavp/SHA256ShortMsg.rsp`.
- 64 vectors from `cavp/SHA256LongMsg.rsp`.
- 2 examples from FIPS 180-2, Appendix B.

That is 131 distinct vectors.

The files are parsed at import time.

Every digest is then checked against `hashlib`.

So a parsing bug fails collection, not a single test.
"""
import hashlib
from pathlib import Path

# The vendored NIST files sit next to this module.
_CAVP_DIR = Path(__file__).resolve().parent / "cavp"

# The SHA-256 examples of FIPS 180-2, Appendix B, with their published digests.
#
# - B.1 is a one-block message.
# - B.2 is a 56-byte message.
#   Its padding does not fit in the first block, so it needs two.
_FIPS_EXAMPLES = [
    ("hash_case_fips_abc", "abc",
     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("hash_case_fips_56_bytes",
     "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
]


def _parse_rsp(path: Path, kind: str) -> list[tuple[str, bytes, bytes]]:
    """The (case name, message, digest) triples of one CAVP `.rsp` file.

    Each case is three lines:

    ```text
    Len = 24        the message length, in bits
    Msg = 616263    the message, in hexadecimal
    MD  = ba78...   the digest, in hexadecimal
    ```

    The length decides how many bytes the message holds.
    """
    cases = []
    # The fields of the case being read, reset after each digest.
    len_bits: int | None = None
    msg_hex: str | None = None
    for line in path.read_text().splitlines():
        # Skip comments, headers and blank lines: they have no " = ".
        key, sep, value = line.partition(" = ")
        if not sep:
            continue
        key, value = key.strip(), value.strip()
        if key == "Len":
            len_bits = int(value)
        elif key == "Msg":
            msg_hex = value
        elif key == "MD":
            # The digest closes a case, so both other fields must be set.
            if len_bits is None or msg_hex is None:
                raise ValueError(f"{path.name}: MD without Len or Msg")
            # The byte-oriented files hold whole bytes only.
            if len_bits % 8 != 0:
                raise ValueError(f"{path.name}: Len {len_bits} is not a whole byte")
            # Why truncate: the empty message is written as one placeholder byte.
            #
            #     Len = 0, Msg = 00  ->  message b""
            message = bytes.fromhex(msg_hex)[: len_bits // 8]
            cases.append((f"hash_case_{kind}_len_{len_bits}", message,
                          bytes.fromhex(value)))
            len_bits, msg_hex = None, None
    return cases


def _vectors() -> list[tuple[str, bytes, bytes]]:
    """Every case, in order: short messages, long messages, then the examples."""
    cases = _parse_rsp(_CAVP_DIR / "SHA256ShortMsg.rsp", "short")
    cases += _parse_rsp(_CAVP_DIR / "SHA256LongMsg.rsp", "long")
    cases += [(name, msg.encode(), bytes.fromhex(md))
              for name, msg, md in _FIPS_EXAMPLES]
    # Invariant: no message appears twice.
    #
    # A duplicate would pin the same vector under two case names.
    messages = [message for _, message, _ in cases]
    assert len(set(messages)) == len(messages), "duplicate SHA-256 message"
    # Invariant: no case name appears twice.
    #
    # Two cases with one name would write the same output directory.
    names = [name for name, _, _ in cases]
    assert len(set(names)) == len(names), "duplicate SHA-256 case name"
    return cases


_CASES = _vectors()

# The case names, one output directory each.
CASE_NAMES: list[str] = [name for name, _, _ in _CASES]

# The (message, digest) pairs, in the same order as the names.
VECTORS: list[tuple[bytes, bytes]] = [(message, digest)
                                      for _, message, digest in _CASES]

# An independent implementation vouches for every digest.
assert all(hashlib.sha256(message).digest() == digest
           for message, digest in VECTORS)
