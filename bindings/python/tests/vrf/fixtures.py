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
OUTPUT_ZERO = bytes.fromhex("a4de0b38b395e4b742d9ab39fd58bdb5b5ae61dab57359aa26db11d1fee1a4c2")

# The opening at index 2^32 - 1, its root and its output.
INDEX_LAST = 0xFFFF_FFFF
OPENING_LAST = pattern_opening(13, 5, 31, 3, 1)
ROOT_LAST = bytes.fromhex("2c490d4de0e4bea851faa8e58c8d8654899ccd22bb10fb82cb6978d926712511")
OUTPUT_LAST = bytes.fromhex("6c297a1b1ad80588bca7636afc90cac946b7112ae8a9a5c11aa7d76deff99cb9")


# ---- Seeds -------------------------------------------------------------------

# Byte k of the seed is 17 k + 9 mod 256.
SEED = bytes((17 * k + 9) % 256 for k in range(32))

# The secret and the output at index 0 and at index 2^32 - 1, from that seed.
SECRET_ZERO = bytes.fromhex("139cc9c398fc8aab72bb6ec83f8213579dd217479fcd0a1b536dbaec424ee1ac")
OUTPUT_SEED_ZERO = bytes.fromhex("dc5ae8af27a545fbccdad5f6344767b5783400da170b00f543d32816f8bc094b")
SECRET_LAST = bytes.fromhex("49306ebca12a70665becbaf9bec13453b4c253a9883bb81115a02d9dbc58f6d2")
OUTPUT_SEED_LAST = bytes.fromhex("e16cdef6c3009b4b2576fe6ea49b13ae712e973bc87709d7b2fe97911c95e205")

# Byte k of the randomness of the mix is 7 k + 1 mod 256.
RANDOMNESS = bytes((7 * k + 1) % 256 for k in range(32))

# The output at index 0 of the opening above, mixed with that randomness.
MIX_ZERO = bytes.fromhex("df8660355cf6c1c23ce0aa1e9e4befa5f1bd4cfd989a9dc7c369748afbc67452")
