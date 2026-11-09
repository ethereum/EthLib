"""RFC 7748 X25519 test vectors and decoding rules through the bindings."""

import os

import pytest

from ethlib.cryptography.x25519 import X25519Error, x25519, x25519_public_key
from raising import raises

# RFC 7748, A. Langley, M. Hamburg and S. Turner, January 2016: extracted vectors begin.
# Copyright (c) 2016 IETF Trust and the persons identified as authors of the code.
# All rights reserved.
# Redistribution and use in source and binary forms, with or without modification, is permitted pursuant to, and subject to the license terms contained in, the Revised BSD License set forth in Section 4.c of the IETF Trust’s Legal Provisions Relating to IETF Documents (https://trustee.ietf.org/license-info).  # noqa: E501
# Source: https://www.rfc-editor.org/rfc/rfc7748#section-5.2
X25519_VECTORS = [
    (
        "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
        "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
        "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552",
    ),
    (
        "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
        "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
        "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957",
    ),
]
ITERATIONS = [
    (1, "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079"),
    (1000, "684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51"),
    pytest.param(
        1000000,
        "7c3911e0ab2586fd864497297e575e6f3bc601c0883c30df5f4dd2d24f665424",
        marks=pytest.mark.skipif(
            os.environ.get("ETHLIB_SLOW_VECTORS") != "1",
            reason="set ETHLIB_SLOW_VECTORS=1 for the million-iteration RFC 7748 vector",
        ),
    ),
]
# Source: https://www.rfc-editor.org/rfc/rfc7748#section-6.1
ALICE = bytes.fromhex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
ALICE_PUBLIC = bytes.fromhex("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
BOB = bytes.fromhex("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
BOB_PUBLIC = bytes.fromhex("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
SHARED = bytes.fromhex("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")
# RFC 7748 extracted vectors end.


@pytest.mark.parametrize(("scalar", "u", "expected"), X25519_VECTORS)
def test_x25519(scalar: str, u: str, expected: str) -> None:
    assert x25519(bytes.fromhex(scalar), bytes.fromhex(u)) == bytes.fromhex(expected)


@pytest.mark.parametrize(("count", "expected"), ITERATIONS)
def test_x25519_iterations(count: int, expected: str) -> None:
    scalar = u = b"\x09" + bytes(31)
    for _ in range(count):
        scalar, u = x25519(scalar, u), scalar
    assert scalar == bytes.fromhex(expected)


def test_agreement() -> None:
    assert x25519_public_key(ALICE) == ALICE_PUBLIC
    assert x25519_public_key(BOB) == BOB_PUBLIC
    assert x25519(ALICE, BOB_PUBLIC) == SHARED
    assert x25519(BOB, ALICE_PUBLIC) == SHARED


@pytest.mark.parametrize("n", range(19))
def test_noncanonical_coordinate(n: int) -> None:
    assert x25519(ALICE, ((1 << 255) - 19 + n).to_bytes(32, "little")) == x25519(
        ALICE, n.to_bytes(32, "little")
    )


def test_mask_and_clamp() -> None:
    assert x25519(ALICE, BOB_PUBLIC[:-1] + bytes([BOB_PUBLIC[-1] | 128])) == SHARED
    clamped_equivalent = bytes([ALICE[0] ^ 7]) + ALICE[1:-1] + bytes([ALICE[-1] ^ 192])
    assert x25519(clamped_equivalent, BOB_PUBLIC) == SHARED
    assert x25519(ALICE, bytes(32)) == bytes(32)


def test_sizes() -> None:
    with raises(X25519Error, "expected 32 bytes, got 31"):
        x25519(bytes(31), bytes(32))
    with raises(X25519Error, "expected 32 bytes, got 33"):
        x25519_public_key(bytes(33))
