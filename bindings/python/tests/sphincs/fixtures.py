"""
Inputs shared by the leanSPHINCS test-vector generators.

Key generation builds the top tree, `2^10` one-time keys, and signing builds
the FORS key and three trees, which takes the compiled specification seconds
per case.

So their cases are written only when `ETHLIB_SLOW_VECTORS=1`, and every other
run reads the committed ones back.
"""

import os

import pytest
from ruamel.yaml import YAML

from dumper import ROOT


# ---- Slow cases ------------------------------------------------------------

# Key generation and signing run only on request.
SLOW = os.environ.get("ETHLIB_SLOW_VECTORS") == "1"

slow = pytest.mark.skipif(not SLOW, reason="set ETHLIB_SLOW_VECTORS=1 to regenerate")


# ---- Seeds and messages ----------------------------------------------------

# The seed of the known answer the proofs pin: byte i is 37 i + 11 mod 256.
SEED_KNOWN_ANSWER = bytes((37 * i + 11) % 256 for i in range(32))

# The all-zero seed, a second key.
SEED_ZERO = bytes(32)

# The message of the known answer: byte i is 7 i + 3.
MESSAGE_KNOWN_ANSWER = bytes(7 * i + 3 for i in range(32))

# The all-zero message, which the digest sends to another FORS instance.
MESSAGE_ZERO = bytes(32)


# ---- Committed cases -------------------------------------------------------

def read_output(handler: str, case: str) -> bytes:
    """The output bytes of a committed case."""
    data = YAML(typ="safe").load((ROOT / "sphincs" / handler / case / "data.yaml").read_text())
    return bytes.fromhex(data["output"].removeprefix("0x"))


def flip(data: bytes, offset: int) -> bytes:
    """The same bytes with the low bit of one byte flipped."""
    out = bytearray(data)
    out[offset] ^= 1
    return bytes(out)
