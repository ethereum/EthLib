"""
The Keccak team's Keccak-256 test vectors, as (message, digest) pairs.

They are the byte-aligned cases of `kat/ShortMsgKAT_256.txt`, 256 vectors from 0 to 255 bytes.

The file is parsed at import time, so a parsing bug fails collection, not a single test.

No independent Keccak-256 is in the Python standard library, so the digests are the file's own.
"""
from pathlib import Path

# The vendored file sits next to this module.
_KAT_FILE = Path(__file__).resolve().parent / "kat" / "ShortMsgKAT_256.txt"


def _parse_kat(path: Path) -> list[tuple[str, bytes, bytes]]:
    """The (case name, message, digest) triples of the byte-aligned cases.

    Each case is three lines:

    ```text
    Len = 24        the message length, in bits
    Msg = 616263    the message, in hexadecimal
    MD = 4E03...    the digest, in hexadecimal
    ```

    A case whose length is not a whole number of bytes is skipped.
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
            if len_bits % 8 == 0:
                # Why truncate: the empty message is written as one placeholder byte.
                #
                #     Len = 0, Msg = 00  ->  message b""
                message = bytes.fromhex(msg_hex)[: len_bits // 8]
                cases.append((f"hash_case_short_len_{len_bits}", message, bytes.fromhex(value)))
            len_bits, msg_hex = None, None
    return cases


_CASES = _parse_kat(_KAT_FILE)

# Invariant: the file holds one byte-aligned case per byte length from 0 to 255.
assert [len(message) for _, message, _ in _CASES] == list(range(256)), "unexpected cases"

# The case names, one output directory each.
CASE_NAMES: list[str] = [name for name, _, _ in _CASES]

# The (message, digest) pairs, in the same order as the names.
VECTORS: list[tuple[bytes, bytes]] = [(message, digest) for _, message, digest in _CASES]
