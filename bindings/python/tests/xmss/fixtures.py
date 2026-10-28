"""
Inputs shared by the leanXMSS test-vector generators.

Key generation and signing build `2^16` one-time keys per tree, which takes the
compiled specification minutes per case.

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


# ---- Leaf indices ----------------------------------------------------------

# The leaf index of the known answer, in bottom tree 0xA5C3.
#
#     0xA5C3_7E19 = bottom tree 0xA5C3, leaf 0x7E19 inside it
LEAF_KNOWN_ANSWER = 0xA5C3_7E19

# The first leaf of the first bottom tree.
LEAF_FIRST = 0

# The first leaf of the second bottom tree, so the top key changes.
LEAF_SECOND_TREE = 1 << 16

# The last leaf of the last bottom tree.
LEAF_LAST = (1 << 32) - 1


# ---- Committed cases -------------------------------------------------------

def read_output(handler: str, case: str) -> bytes:
    """The output bytes of a committed case."""
    data = YAML(typ="safe").load((ROOT / "xmss" / handler / case / "data.yaml").read_text())
    return bytes.fromhex(data["output"].removeprefix("0x"))


def flip(data: bytes, offset: int) -> bytes:
    """The same bytes with the low bit of one byte flipped."""
    out = bytearray(data)
    out[offset] ^= 1
    return bytes(out)
