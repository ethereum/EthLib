"""
Reference operations come from `py_ecc.bls.G2ProofOfPossession`.
"""

from typing import cast

from eth_typing import BLSSignature
from py_ecc.bls import G2ProofOfPossession as RefBls

# ---- Messages -------------------------------------------------------------

MESSAGES = [
    b"\x00" * 32,
    b"\x56" * 32,
    b"\xab" * 32,
]
SAMPLE_MESSAGE = b"\x12" * 32


# ---- Private keys ---------------------------------------------------------

PRIVKEYS = [
    0x263DBD792F5B1BE47ED85F8938C0F29586AF0D3AC7B977F21C278FE1462040E3,
    0x47B8192D77BF871B62E87859D653922725724A5C031AFEABC60BCEF5FF665138,
    0x328388AFF0D4A5B7DC9205ABD374E7E98F3CD9F3418EDB4EAFDA5FB16473D216,
]


# ---- Compressed-G group encodings ----------------------------------------

ZERO_PUBKEY = b"\x00" * 48
G1_POINT_AT_INFINITY = b"\xc0" + b"\x00" * 47
ZERO_SIGNATURE = b"\x00" * 96
G2_POINT_AT_INFINITY = b"\xc0" + b"\x00" * 95


# ---- Helpers --------------------------------------------------------------


def sk_to_pk(sk: int) -> bytes:
    return RefBls.SkToPk(sk)


def sign(sk: int, msg: bytes) -> bytes:
    return RefBls.Sign(sk, msg)


def aggregate(sigs: list[bytes]) -> bytes:
    # The reference types its signatures as BLSSignature, and a list is invariant.
    return RefBls.Aggregate(cast(list[BLSSignature], sigs))
