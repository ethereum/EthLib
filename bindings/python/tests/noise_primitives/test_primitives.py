"""RFC 7748 X25519 and every RFC 8439 algorithm test vector through the bindings."""

import json
import os
from pathlib import Path

import pytest

from ethlib.cryptography.noise_primitives import (
    chacha20_block,
    chacha20_crypt,
    chacha20_poly1305_decrypt,
    chacha20_poly1305_encrypt,
    chacha20_quarter_round,
    chacha20_quarter_round_state,
    poly1305,
    poly1305_key,
    x25519,
    x25519_public_key,
)
from ethlib.errors import ChaCha20Poly1305Error, X25519Error
from raising import raises

RFC = json.loads(Path(__file__).with_name("rfc8439.json").read_text())


@pytest.mark.parametrize("case", RFC["blocks"], ids=lambda case: case["section"])
def test_block(case: dict) -> None:
    assert chacha20_block(
        bytes.fromhex(case["key"]), case["counter"], bytes.fromhex(case["nonce"])
    ) == bytes.fromhex(case["output"])


@pytest.mark.parametrize("case", RFC["streams"], ids=lambda case: case["section"])
def test_stream(case: dict) -> None:
    key, nonce = bytes.fromhex(case["key"]), bytes.fromhex(case["nonce"])
    plain, cipher = bytes.fromhex(case["input"]), bytes.fromhex(case["output"])
    assert chacha20_crypt(key, case["counter"], nonce, plain) == cipher
    assert chacha20_crypt(key, case["counter"], nonce, cipher) == plain


@pytest.mark.parametrize("case", RFC["macs"], ids=lambda case: case["section"])
def test_mac(case: dict) -> None:
    assert poly1305(bytes.fromhex(case["key"]), bytes.fromhex(case["input"])) == bytes.fromhex(
        case["output"]
    )


@pytest.mark.parametrize("case", RFC["keygen"], ids=lambda case: case["section"])
def test_poly1305_key(case: dict) -> None:
    assert poly1305_key(bytes.fromhex(case["key"]), bytes.fromhex(case["nonce"])) == bytes.fromhex(
        case["output"]
    )


@pytest.mark.parametrize("case", RFC["aead"], ids=lambda case: case["section"])
def test_aead(case: dict) -> None:
    key, nonce, aad = (bytes.fromhex(case[k]) for k in ("key", "nonce", "aad"))
    plain, cipher, tag = (bytes.fromhex(case[k]) for k in ("plaintext", "ciphertext", "tag"))
    assert chacha20_poly1305_encrypt(key, nonce, aad, plain) == (cipher, tag)
    assert chacha20_poly1305_decrypt(key, nonce, aad, cipher, tag) == plain


# RFC 8439, Y. Nir and A. Langley, June 2018: extracted quarter-round vectors begin.
# Copyright (c) 2018 IETF Trust and the persons identified as authors of the code.
# All rights reserved.
# Redistribution and use in source and binary forms, with or without modification, is permitted pursuant to, and subject to the license terms contained in, the Revised BSD License set forth in Section 4.c of the IETF Trust’s Legal Provisions Relating to IETF Documents (https://trustee.ietf.org/license-info).  # noqa: E501
# Source: https://www.rfc-editor.org/rfc/rfc8439#section-2.1.1
def test_quarter_round() -> None:
    assert chacha20_quarter_round(0x11111111, 0x01020304, 0x9B8D6F43, 0x01234567) == (
        0xEA2A92F4,
        0xCB1CF8CE,
        0x4581472E,
        0x5881C4BB,
    )


# Source: https://www.rfc-editor.org/rfc/rfc8439#section-2.2.1
def test_quarter_round_state() -> None:
    before = [
        0x879531E0,
        0xC5ECF37D,
        0x516461B1,
        0xC9A62F8A,
        0x44C20EF3,
        0x3390AF7F,
        0xD9FC690B,
        0x2A5F714C,
        0x53372767,
        0xB00A5631,
        0x974C541A,
        0x359E9963,
        0x5C971061,
        0x3D631689,
        0x2098D9D6,
        0x91DBD320,
    ]
    after = before.copy()
    after[2], after[7], after[8], after[13] = 0xBDB886DC, 0xCFACAFD2, 0xE46BEA80, 0xCCC07C79
    assert chacha20_quarter_round_state(
        b"".join(n.to_bytes(4, "little") for n in before), 2, 7, 8, 13
    ) == b"".join(n.to_bytes(4, "little") for n in after)


# RFC 8439 extracted quarter-round vectors end.


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


@pytest.mark.parametrize("length", [0, 1, 15, 16, 17, 63, 64, 65])
@pytest.mark.parametrize("aad_length", [0, 1, 15, 16, 17])
def test_aead_boundaries(length: int, aad_length: int) -> None:
    key, nonce = bytes(range(32)), bytes(range(12))
    aad, plain = bytes(range(aad_length)), bytes(range(length))
    cipher, tag = chacha20_poly1305_encrypt(key, nonce, aad, plain)
    assert len(cipher) == length
    assert len(tag) == 16
    assert chacha20_poly1305_decrypt(key, nonce, aad, cipher, tag) == plain
    for i in range(len(tag)):
        bad = tag[:i] + bytes([tag[i] ^ 1]) + tag[i + 1 :]
        with raises(
            ChaCha20Poly1305Error,
            "EthLib.Cryptography.ChaCha20Poly1305.CipherError.authenticationFailed",
        ):
            chacha20_poly1305_decrypt(key, nonce, aad, cipher, bad)


def test_counter_exhaustion() -> None:
    key, nonce = bytes(32), bytes(12)
    assert chacha20_crypt(key, (1 << 32) - 1, nonce, b"") == b""
    assert len(chacha20_crypt(key, (1 << 32) - 1, nonce, bytes(64))) == 64
    with raises(
        ChaCha20Poly1305Error,
        "EthLib.Cryptography.ChaCha20Poly1305.CipherError.counterExhausted",
    ):
        chacha20_crypt(key, (1 << 32) - 1, nonce, bytes(65))


@pytest.mark.parametrize("field", ["key", "nonce", "aad", "ciphertext"])
def test_authentication_binds_inputs(field: str) -> None:
    case = RFC["aead"][0]
    args = {name: bytes.fromhex(case[name]) for name in ("key", "nonce", "aad", "ciphertext")}
    value = args[field]
    args[field] = bytes([value[0] ^ 1]) + value[1:]
    with raises(
        ChaCha20Poly1305Error,
        "EthLib.Cryptography.ChaCha20Poly1305.CipherError.authenticationFailed",
    ):
        chacha20_poly1305_decrypt(
            args["key"], args["nonce"], args["aad"], args["ciphertext"], bytes.fromhex(case["tag"])
        )


def test_sizes() -> None:
    with raises(X25519Error, "expected 32 bytes, got 31"):
        x25519(bytes(31), bytes(32))
    with raises(ChaCha20Poly1305Error, "expected 12 bytes, got 11"):
        chacha20_poly1305_encrypt(bytes(32), bytes(11), b"", b"")
    with raises(ChaCha20Poly1305Error, "expected 16 bytes, got 15"):
        chacha20_poly1305_decrypt(bytes(32), bytes(12), b"", b"", bytes(15))
