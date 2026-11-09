"""Every RFC 8439 algorithm test vector and the AEAD boundaries through the bindings."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography.chacha20_poly1305 import (
    ChaCha20Poly1305Error,
    chacha20_block,
    chacha20_crypt,
    chacha20_poly1305_decrypt,
    chacha20_poly1305_encrypt,
    chacha20_quarter_round,
    chacha20_quarter_round_state,
    poly1305,
    poly1305_key,
)
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
            "EthLib.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305Error.authenticationFailed",
        ) as error:
            chacha20_poly1305_decrypt(key, nonce, aad, cipher, bad)
        assert error.value.code == 3


def test_counter_exhaustion() -> None:
    key, nonce = bytes(32), bytes(12)
    assert chacha20_crypt(key, (1 << 32) - 1, nonce, b"") == b""
    assert len(chacha20_crypt(key, (1 << 32) - 1, nonce, bytes(64))) == 64
    with raises(
        ChaCha20Poly1305Error,
        "EthLib.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305Error.counterExhausted",
    ) as error:
        chacha20_crypt(key, (1 << 32) - 1, nonce, bytes(65))
    assert error.value.code == 1


@pytest.mark.parametrize("field", ["key", "nonce", "aad", "ciphertext"])
def test_authentication_binds_inputs(field: str) -> None:
    case = RFC["aead"][0]
    args = {name: bytes.fromhex(case[name]) for name in ("key", "nonce", "aad", "ciphertext")}
    value = args[field]
    args[field] = bytes([value[0] ^ 1]) + value[1:]
    with raises(
        ChaCha20Poly1305Error,
        "EthLib.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305Error.authenticationFailed",
    ) as error:
        chacha20_poly1305_decrypt(
            args["key"], args["nonce"], args["aad"], args["ciphertext"], bytes.fromhex(case["tag"])
        )
    assert error.value.code == 3


def test_sizes() -> None:
    with raises(ChaCha20Poly1305Error, "expected 12 bytes, got 11"):
        chacha20_poly1305_encrypt(bytes(32), bytes(11), b"", b"")
    with raises(ChaCha20Poly1305Error, "expected 16 bytes, got 15"):
        chacha20_poly1305_decrypt(bytes(32), bytes(12), b"", b"", bytes(15))


@pytest.mark.parametrize("position", range(4))
def test_quarter_round_index_bound(position: int) -> None:
    indices = [0, 1, 2, 3]
    indices[position] = 16
    with raises(ChaCha20Poly1305Error, "quarter-round index must be below 16") as error:
        chacha20_quarter_round_state(bytes(64), *indices)
    assert error.value.code == 0
