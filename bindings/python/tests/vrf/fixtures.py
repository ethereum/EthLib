"""Inputs and expected values shared by the VRF tree test-vector generators."""

# The openings follow byte patterns, so they are written here as functions.
# The roots, the outputs and the secrets were computed outside EthLib.
# An independent implementation of the specification computed them.


# ---- Openings ----------------------------------------------------------------


def pattern_opening(sa: int, sb: int, pa: int, pb: int, pc: int) -> bytes:
    """The 1056 bytes of an opening whose secret and siblings follow two byte patterns."""
    # Byte k of the secret is (sa k + sb) mod 256.
    # Byte k of sibling l is (pa l + pb k + pc) mod 256.
    # The siblings follow the secret, from the leaf up to the root.
    secret = bytes((sa * k + sb) % 256 for k in range(32))
    path = b"".join(bytes((pa * row + pb * k + pc) % 256 for k in range(32)) for row in range(32))
    return secret + path


def flip(data: bytes, offset: int) -> bytes:
    """The same bytes with the low bit of one byte flipped."""
    out = bytearray(data)
    out[offset] ^= 1
    return bytes(out)


# The opening at index 0, its root and its output.
INDEX_ZERO = 0
OPENING_ZERO = pattern_opening(37, 11, 29, 7, 3)
ROOT_ZERO = bytes.fromhex("6ec3c3f7506bc50c9060055d06367f4496796766d6843db8e71f7e6ba32b17ba")
OUTPUT_ZERO = bytes.fromhex("8c45984a8f204a78f878fe9e44601a44a873a97f669e816b633e636a44330b93")

# The opening at index 2^32 - 1, its root and its output.
INDEX_LAST = 0xFFFF_FFFF
OPENING_LAST = pattern_opening(13, 5, 31, 3, 1)
ROOT_LAST = bytes.fromhex("2c490d4de0e4bea851faa8e58c8d8654899ccd22bb10fb82cb6978d926712511")
OUTPUT_LAST = bytes.fromhex("f9e8d5c30980ce4c733388a53003de4136c44f8829395369b1644b222bbfcdf9")


# ---- Seeds -------------------------------------------------------------------

# Byte k of the seed is 17 k + 9 mod 256.
SEED = bytes((17 * k + 9) % 256 for k in range(32))

# The secret and the output at index 0 and at index 2^32 - 1, from that seed.
SECRET_ZERO = bytes.fromhex("139cc9c398fc8aab72bb6ec83f8213579dd217479fcd0a1b536dbaec424ee1ac")
OUTPUT_SEED_ZERO = bytes.fromhex("c37ea9b168dc9033f30df8f16126f1cb2952203ba9408e77ec482704692f7f50")
SECRET_LAST = bytes.fromhex("49306ebca12a70665becbaf9bec13453b4c253a9883bb81115a02d9dbc58f6d2")
OUTPUT_SEED_LAST = bytes.fromhex("ba9e181f73e4449b96bf181ed8349c9ee911d0c52e552f677fbc8ee3edc331df")
