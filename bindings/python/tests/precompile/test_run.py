"""Every precompile through the one entry point, against an independent oracle.

The prices are those of Fusaka, the fork `osaka` of execution-specs.

Repository: ethereum/execution-specs
Commit: e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e
Path: src/ethereum/forks/osaka/vm/precompiled_contracts
"""

import hashlib
import struct

import pytest

from ethlib.precompiles import ADDRESSES, run
from ethlib.precompiles import ecrecover as ecrecover_precompile
from ethlib.precompiles import modexp as modexp_precompile


def word(value: int) -> bytes:
    return value.to_bytes(32, "big")


def test_addresses() -> None:
    assert ADDRESSES == tuple(range(0x01, 0x12)) + (0x100,)


@pytest.mark.parametrize("address", [0x00, 0x12, 0xFF, 0x101, 2**64 - 1])
def test_unknown_address(address: int) -> None:
    with pytest.raises(ValueError, match="no precompile at address"):
        run(address, b"", 10**6)


def test_rejects_bad_arguments() -> None:
    with pytest.raises(TypeError):
        run(0x04, "abc", 100)  # type: ignore[arg-type]
    with pytest.raises(OverflowError):
        run(0x04, b"", 2**64)


def test_ecrecover() -> None:
    # The same call through the dedicated binding gives the same output.
    data = bytes(range(128))
    assert run(0x01, data, 3000) == ecrecover_precompile.ecrecover(data, 3000)
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x01, data, 2999)


def test_sha256() -> None:
    assert run(0x02, b"abc", 72) == hashlib.sha256(b"abc").digest()
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x02, b"abc", 71)


@pytest.mark.parametrize("data, digest, price", [
    # The digests are those of the RIPEMD-160 paper, Appendix B.
    (b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31", 600),
    (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc", 720),
    (b"a" * 33, None, 840),
])
def test_ripemd160(data: bytes, digest: str | None, price: int) -> None:
    # The price is 600, plus 120 per started 32-byte word.
    out = run(0x03, data, price)
    assert out[:12] == bytes(12)
    if digest is not None:
        assert out[12:].hex() == digest
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x03, data, price - 1)


@pytest.mark.parametrize("size, price", [(0, 15), (33, 21)])
def test_identity(size: int, price: int) -> None:
    # The price is 15, plus 3 per started 32-byte word.
    data = bytes(range(size))
    assert run(0x04, data, price) == data
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x04, data, price - 1)


def test_modexp() -> None:
    # 3^(p - 2) mod p for the prime p = 2^255 - 19, through the dedicated binding and through Python.
    p = 2**255 - 19
    data = word(1) + word(32) + word(32) + bytes([3]) + word(p - 2) + word(p)
    price = modexp_precompile.gas_cost(data)
    assert run(0x05, data, price) == word(pow(3, p - 2, p))
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x05, data, price - 1)


def blake2f_input(rounds: int, message: bytes, final: int) -> bytes:
    """The 213-byte BLAKE2F input that compresses one block of an unkeyed 64-byte BLAKE2b hash."""
    iv = [
        0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
        0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179,
    ]
    # The parameter block of RFC 7693 §2.5: digest length 64, no key, fanout 1, depth 1.
    h = [iv[0] ^ 0x01010040] + iv[1:]
    block = message.ljust(128, b"\0")
    return (struct.pack(">I", rounds) + struct.pack("<8Q", *h) + block
            + struct.pack("<2Q", len(message), 0) + bytes([final]))


def test_blake2f() -> None:
    # With 12 rounds and the final flag, F on the one block of "abc" is the whole BLAKE2b-512 hash.
    data = blake2f_input(12, b"abc", 1)
    assert run(0x09, data, 12) == hashlib.blake2b(b"abc").digest()
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x09, data, 11)


def test_blake2f_order_of_checks() -> None:
    # The length is checked before the gas, and the gas before the flag.
    with pytest.raises(ValueError, match="invalidLength"):
        run(0x09, blake2f_input(12, b"abc", 1)[:-1], 0)
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x09, blake2f_input(12, b"abc", 2), 11)
    with pytest.raises(ValueError, match="invalidFlag"):
        run(0x09, blake2f_input(12, b"abc", 2), 12)


@pytest.mark.parametrize("address, size, price, out_size", [
    # The sum of two points at infinity is the point at infinity.
    (0x0B, 256, 375, 128),
    (0x0D, 512, 600, 256),
])
def test_bls12_add_infinity(address: int, size: int, price: int, out_size: int) -> None:
    assert run(address, bytes(size), price) == bytes(out_size)
    with pytest.raises(ValueError, match="outOfGas"):
        run(address, bytes(size), price - 1)


@pytest.mark.parametrize("address, size, price, out_size", [
    (0x10, 64, 5500, 128),
    (0x11, 128, 23800, 256),
])
def test_bls12_map_zero(address: int, size: int, price: int, out_size: int) -> None:
    # The zero field element maps to a point, which the EIP-2537 vectors fix.
    assert len(run(address, bytes(size), price)) == out_size
    with pytest.raises(ValueError, match="outOfGas"):
        run(address, bytes(size), price - 1)
