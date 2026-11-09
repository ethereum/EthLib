"""Password-based key derivation against RFC 7914 and Python's independent implementation."""

import hashlib
import os

import pytest

from ethlib.cryptography.kdf import pbkdf2, salsa208, scrypt, scrypt_block_mix, scrypt_romix
from ethlib.errors import Pbkdf2Error, ScryptError
from raising import raises

# RFC 7914, C. Percival and S. Josefsson, August 2016: extracted test vectors begin.
# Copyright (c) 2016 IETF Trust and the persons identified as authors of the code.
# All rights reserved.
# Redistribution and use in source and binary forms, with or without modification, is permitted pursuant to, and subject to the license terms contained in, the Revised BSD License set forth in Section 4.c of the IETF Trust’s Legal Provisions Relating to IETF Documents (https://trustee.ietf.org/license-info).  # noqa: E501

# RFC 7914 §8: https://www.rfc-editor.org/rfc/rfc7914#section-8
SALSA_INPUT = bytes.fromhex("""
    7e 87 9a 21 4f 3e c9 86 7c a9 40 e6 41 71 8f 26
    ba ee 55 5b 8c 61 c1 b5 0d f8 46 11 6d cd 3b 1d
    ee 24 f3 19 df 9b 3d 85 14 12 1e 4b 5a c5 aa 32
    76 02 1d 29 09 c7 48 29 ed eb c6 8d b8 b8 c2 5e
""")
SALSA_OUTPUT = bytes.fromhex("""
    a4 1f 85 9c 66 08 cc 99 3b 81 ca cb 02 0c ef 05
    04 4b 21 81 a2 fd 33 7d fd 7b 1c 63 96 68 2f 29
    b4 39 31 68 e3 c9 e6 bc fe 6b c5 b7 a0 6d 96 ba
    e4 24 cc 10 2c 91 74 5c 24 ad 67 3d c7 61 8f 81
""")

# RFC 7914 §9: https://www.rfc-editor.org/rfc/rfc7914#section-9
BLOCK_INPUT = bytes.fromhex("""
    f7 ce 0b 65 3d 2d 72 a4 10 8c f5 ab e9 12 ff dd
    77 76 16 db bb 27 a7 0e 82 04 f3 ae 2d 0f 6f ad
    89 f6 8f 48 11 d1 e8 7b cc 3b d7 40 0a 9f fd 29
    09 4f 01 84 63 95 74 f3 9a e5 a1 31 52 17 bc d7
    89 49 91 44 72 13 bb 22 6c 25 b5 4d a8 63 70 fb
    cd 98 43 80 37 46 66 bb 8f fc b5 bf 40 c2 54 b0
    67 d2 7c 51 ce 4a d5 fe d8 29 c9 0b 50 5a 57 1b
    7f 4d 1c ad 6a 52 3c da 77 0e 67 bc ea af 7e 89
""")
BLOCK_OUTPUT = bytes.fromhex("""
    a4 1f 85 9c 66 08 cc 99 3b 81 ca cb 02 0c ef 05
    04 4b 21 81 a2 fd 33 7d fd 7b 1c 63 96 68 2f 29
    b4 39 31 68 e3 c9 e6 bc fe 6b c5 b7 a0 6d 96 ba
    e4 24 cc 10 2c 91 74 5c 24 ad 67 3d c7 61 8f 81
    20 ed c9 75 32 38 81 a8 05 40 f6 4c 16 2d cd 3c
    21 07 7c fe 5f 8d 5f e2 b1 a4 16 8f 95 36 78 b7
    7d 3b 3d 80 3b 60 e4 ab 92 09 96 e5 9b 4d 53 b6
    5d 2a 22 58 77 d5 ed f5 84 2c b9 f1 4e ef e4 25
""")

# RFC 7914 §10: https://www.rfc-editor.org/rfc/rfc7914#section-10
ROMIX_OUTPUT = bytes.fromhex("""
    79 cc c1 93 62 9d eb ca 04 7f 0b 70 60 4b f6 b6
    2c e3 dd 4a 96 26 e3 55 fa fc 61 98 e6 ea 2b 46
    d5 84 13 67 3b 99 b0 29 d6 65 c3 57 60 1f b4 26
    a0 b2 f4 bb a2 00 ee 9f 0a 43 d1 9b 57 1a 9c 71
    ef 11 42 e6 5d 5a 26 6f dd ca 83 2c e5 9f aa 7c
    ac 0b 9c f1 be 2b ff ca 30 0d 01 ee 38 76 19 c4
    ae 12 fd 44 38 f2 03 a0 e4 e1 c4 7e c3 14 86 1f
    4e 90 87 cb 33 39 6a 68 73 e8 f9 d2 53 9a 4b 8e
""")

# RFC 7914 §11: https://www.rfc-editor.org/rfc/rfc7914#section-11
PBKDF2_VECTORS = [
    (
        b"passwd",
        b"salt",
        1,
        "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc"
        "49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783",
    ),
    (
        b"Password",
        b"NaCl",
        80000,
        "4ddcd8f60b98be21830cee5ef22701f9641a4418d04c0414aeff08876b34ab56"
        "a1d425a1225833549adb841b51c9b3176a272bdebba1d078478f62b397f33c8d",
    ),
]

# RFC 7914 §12: https://www.rfc-editor.org/rfc/rfc7914#section-12
SCRYPT_VECTORS = [
    (
        b"",
        b"",
        16,
        1,
        1,
        "77d6576238657b203b19ca42c18a0497f16b4844e3074ae8dfdffa3fede21442"
        "fcd0069ded0948f8326a753a0fc81f17e8d3e0fb2e0d3628cf35e20c38d18906",
    ),
    (
        b"password",
        b"NaCl",
        1024,
        8,
        16,
        "fdbabe1c9d3472007856e7190d01e9fe7c6ad7cbc8237830e77376634b373162"
        "2eaf30d92e22a3886ff109279d9830dac727afb94a83ee6d8360cbdfa2cc0640",
    ),
    (
        b"pleaseletmein",
        b"SodiumChloride",
        16384,
        8,
        1,
        "7023bdcb3afd7348461c06cd81fd38ebfda8fbba904f8e3ea9b543f6545da1f2"
        "d5432955613f0fcf62d49705242a9af9e61e85dc0d651e40dfcf017b45575887",
    ),
    pytest.param(
        b"pleaseletmein",
        b"SodiumChloride",
        1048576,
        8,
        1,
        "2101cb9b6a511aaeaddbbe09cf70f881ec568d574a2ffd4dabe5ee9820adaa47"
        "8e56fd8f4ba5d09ffa1c6d927c40f4c337304049e8a952fbcbf45c6fa77a41a4",
        marks=pytest.mark.skipif(
            os.environ.get("ETHLIB_SLOW_VECTORS") != "1",
            reason="a 1 GiB table, run weekly with ETHLIB_SLOW_VECTORS=1",
        ),
    ),
]
# RFC 7914 extracted test vectors end.


def test_salsa208_rfc7914() -> None:
    assert salsa208(SALSA_INPUT) == SALSA_OUTPUT


def test_scrypt_block_mix_rfc7914() -> None:
    assert scrypt_block_mix(BLOCK_INPUT, 1) == BLOCK_OUTPUT


def test_scrypt_romix_rfc7914() -> None:
    assert scrypt_romix(BLOCK_INPUT, 16, 1) == ROMIX_OUTPUT


@pytest.mark.parametrize("password, salt, iterations, expected", PBKDF2_VECTORS)
def test_pbkdf2_rfc7914(password: bytes, salt: bytes, iterations: int, expected: str) -> None:
    assert pbkdf2(password, salt, iterations, 64) == bytes.fromhex(expected)


@pytest.mark.parametrize("password, salt, n, r, p, expected", SCRYPT_VECTORS)
def test_scrypt_rfc7914(
    password: bytes, salt: bytes, n: int, r: int, p: int, expected: str
) -> None:
    assert scrypt(password, salt, n, r, p, 64) == bytes.fromhex(expected)


@pytest.mark.parametrize("length", [1, 31, 32, 33, 65])
def test_pbkdf2_binary_input_and_partial_blocks(length: int) -> None:
    # The password exceeds HMAC's block size, and both inputs contain zero bytes.
    password, salt = bytes(range(80)), b"\x00salt\xff"
    assert pbkdf2(password, salt, 3, length) == hashlib.pbkdf2_hmac(
        "sha256", password, salt, 3, length
    )


@pytest.mark.parametrize("length", [1, 31, 32, 33, 65])
def test_scrypt_binary_input_and_partial_blocks(length: int) -> None:
    # r=2 exercises BlockMix's even/odd permutation, and p=2 mixes two input blocks.
    password, salt = bytes(range(80)), b"\x00salt\xff"
    assert scrypt(password, salt, 16, 2, 2, length) == hashlib.scrypt(
        password, salt=salt, n=16, r=2, p=2, dklen=length
    )


def test_scrypt_largest_cost_for_r_1() -> None:
    # RFC 7914 §2 requires N < 2^(16 * r), so N = 2^15 is the largest cost for r = 1.
    password, salt = b"password", b"salt"
    assert scrypt(password, salt, 2**15, 1, 1, 32) == hashlib.scrypt(
        password, salt=salt, n=2**15, r=1, p=1, dklen=32
    )


@pytest.mark.skipif(
    os.environ.get("ETHLIB_SLOW_VECTORS") != "1",
    reason="a 256 MiB table, run weekly with ETHLIB_SLOW_VECTORS=1",
)
def test_scrypt_keystore_cost() -> None:
    # These are the usual scrypt parameters of an Ethereum keystore file.
    password, salt = b"password", b"salt"
    assert scrypt(password, salt, 2**18, 8, 1, 32) == hashlib.scrypt(
        password, salt=salt, n=2**18, r=8, p=1, dklen=32, maxmem=512 * 1024 * 1024
    )


@pytest.mark.parametrize(
    "iterations, length, error",
    [
        (0, 32, "zeroIterations"),
        (1, 0, "emptyOutput"),
        (1, (2**32 - 1) * 32 + 1, "outputTooLong 137438953441"),
    ],
)
def test_pbkdf2_rejects_parameters(iterations: int, length: int, error: str) -> None:
    with raises(Pbkdf2Error, f"EthLib.Cryptography.Hash.Pbkdf2.Pbkdf2Error.{error}"):
        pbkdf2(b"password", b"salt", iterations, length)


@pytest.mark.parametrize(
    "n, r, p, length, error",
    [
        (0, 1, 1, 32, "invalidCost 0"),
        (1, 1, 1, 32, "invalidCost 1"),
        (3, 1, 1, 32, "invalidCost 3"),
        (2**16, 1, 1, 32, "invalidCost 65536"),
        (16, 0, 1, 32, "invalidBlockSize 0"),
        (16, 1, 0, 32, "invalidParallelization 0"),
        (16, 1, 2**30, 32, "invalidParallelization 1073741824"),
        (16, 1, 1, 0, "emptyOutput"),
        (16, 1, 1, (2**32 - 1) * 32 + 1, "outputTooLong 137438953441"),
    ],
)
def test_scrypt_rejects_parameters(n: int, r: int, p: int, length: int, error: str) -> None:
    with raises(ScryptError, f"EthLib.Cryptography.Hash.Scrypt.ScryptError.{error}"):
        scrypt(b"password", b"salt", n, r, p, length)


@pytest.mark.parametrize("size", [0, 63, 65])
def test_salsa208_rejects_input_size(size: int) -> None:
    with raises(
        ScryptError,
        f"EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidInputSize 64 {size}",
    ):
        salsa208(bytes(size))


@pytest.mark.parametrize("size", [127, 129])
def test_scrypt_steps_reject_input_size(size: int) -> None:
    message = f"EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidInputSize 128 {size}"
    with raises(ScryptError, message):
        scrypt_block_mix(bytes(size), 1)
    with raises(ScryptError, message):
        scrypt_romix(bytes(size), 16, 1)


def test_scrypt_steps_reject_zero_block_size() -> None:
    message = "EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidBlockSize 0"
    with raises(ScryptError, message):
        scrypt_block_mix(b"", 0)
    with raises(ScryptError, message):
        scrypt_romix(b"", 16, 0)


@pytest.mark.parametrize("n", [0, 1, 3, 2**16])
def test_scrypt_romix_rejects_cost(n: int) -> None:
    with raises(ScryptError, f"EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidCost {n}"):
        scrypt_romix(BLOCK_INPUT, n, 1)


def test_rejects_non_bytes() -> None:
    with raises(TypeError, "password must be bytes"):
        pbkdf2("password", b"salt", 1, 32)  # ty: ignore[invalid-argument-type]
    with raises(TypeError, "salt must be bytes"):
        scrypt(b"password", "salt", 16, 1, 1, 32)  # ty: ignore[invalid-argument-type]
    with raises(TypeError, "block must be bytes"):
        salsa208("block")  # ty: ignore[invalid-argument-type]
    with raises(TypeError, "block must be bytes"):
        scrypt_block_mix("block", 1)  # ty: ignore[invalid-argument-type]
    with raises(TypeError, "block must be bytes"):
        scrypt_romix("block", 16, 1)  # ty: ignore[invalid-argument-type]


@pytest.mark.parametrize(
    "value, message",
    [(-1, "can't convert negative int to unsigned"), (2**64, "int too big to convert")],
)
def test_rejects_integer_overflow(value: int, message: str) -> None:
    # An integer outside UInt64 must not wrap to a smaller KDF parameter.
    with raises(OverflowError, message):
        pbkdf2(b"password", b"salt", value, 32)
    with raises(OverflowError, message):
        pbkdf2(b"password", b"salt", 1, value)
    with raises(OverflowError, message):
        scrypt(b"password", b"salt", value, 1, 1, 32)
