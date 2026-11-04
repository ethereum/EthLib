"""Every precompile through the one entry point, at every fork, against an independent oracle.

The prices of the first four precompiles are those of Appendix E of the Yellow Paper.
The others are those of the EIP that adds each precompile.
"""

import hashlib
import struct

import pytest

from ethlib.precompiles import ADDRESSES, price, run
from ethlib.precompiles import ecrecover as ecrecover_precompile

from .forks import FORKS, since

# The fork that adds each precompile, from its EIP, and Frontier for the first four.
ADDED = {
    **{address: "frontier" for address in (0x01, 0x02, 0x03, 0x04)},
    **{address: "byzantium" for address in (0x05, 0x06, 0x07, 0x08)},
    0x09: "istanbul",
    0x0A: "dencun",
    **{address: "pectra" for address in range(0x0B, 0x12)},
    0x100: "fusaka",
}


def word(value: int) -> bytes:
    return value.to_bytes(32, "big")


def test_addresses() -> None:
    assert ADDRESSES == tuple(range(0x01, 0x12)) + (0x100,)
    assert set(ADDED) == set(ADDRESSES)


@pytest.mark.parametrize("address", ADDRESSES)
@pytest.mark.parametrize("fork", FORKS)
def test_fork_adds_precompile(fork: str, address: int) -> None:
    # Before the fork that adds it, an address has no precompile, and neither run nor price
    # reaches one.
    if fork in since(ADDED[address]):
        assert price(fork, address, b"") >= 0
    else:
        with pytest.raises(ValueError, match="no precompile at address"):
            run(fork, address, b"", 10**6)
        with pytest.raises(ValueError, match="no precompile at address"):
            price(fork, address, b"")


def test_unknown_fork() -> None:
    with pytest.raises(ValueError, match="no fork named"):
        run("osaka", 0x04, b"", 100)
    with pytest.raises(ValueError, match="no fork named"):
        price("osaka", 0x04, b"")


@pytest.mark.parametrize("address", [0x00, 0x12, 0xFF, 0x101, 2**64 - 1])
@pytest.mark.parametrize("fork", FORKS)
def test_unknown_address(fork: str, address: int) -> None:
    with pytest.raises(ValueError, match="no precompile at address"):
        run(fork, address, b"", 10**6)


def test_rejects_bad_arguments() -> None:
    with pytest.raises(TypeError):
        run("fusaka", 0x04, "abc", 100)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        run(b"fusaka", 0x04, b"", 100)  # type: ignore[arg-type]
    with pytest.raises(OverflowError):
        run("fusaka", 0x04, b"", 2**64)
    with pytest.raises(OverflowError):
        price("fusaka", 2**64, b"")


@pytest.mark.parametrize("fork", FORKS)
def test_ecrecover(fork: str) -> None:
    # The same call through the dedicated binding gives the same output.
    data = bytes(range(128))
    assert run(fork, 0x01, data, 3000) == ecrecover_precompile.ecrecover(data, 3000)
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x01, data, 2999)


@pytest.mark.parametrize("fork", FORKS)
def test_sha256(fork: str) -> None:
    assert run(fork, 0x02, b"abc", 72) == hashlib.sha256(b"abc").digest()
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x02, b"abc", 71)


@pytest.mark.parametrize("data, digest, cost", [
    # The digests are those of the RIPEMD-160 paper, Appendix B.
    (b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31", 600),
    (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc", 720),
    (b"a" * 33, None, 840),
])
@pytest.mark.parametrize("fork", FORKS)
def test_ripemd160(fork: str, data: bytes, digest: str | None, cost: int) -> None:
    # The price is 600, plus 120 per started 32-byte word.
    out = run(fork, 0x03, data, cost)
    assert out[:12] == bytes(12)
    if digest is not None:
        assert out[12:].hex() == digest
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x03, data, cost - 1)


@pytest.mark.parametrize("size, cost", [(0, 15), (33, 21)])
@pytest.mark.parametrize("fork", FORKS)
def test_identity(fork: str, size: int, cost: int) -> None:
    # The price is 15, plus 3 per started 32-byte word.
    data = bytes(range(size))
    assert run(fork, 0x04, data, cost) == data
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x04, data, cost - 1)


@pytest.mark.parametrize("fork", since("byzantium"))
def test_modexp(fork: str) -> None:
    # 3^(p - 2) mod p for the prime p = 2^255 - 19, through the precompile and through Python.
    p = 2**255 - 19
    data = word(1) + word(32) + word(32) + bytes([3]) + word(p - 2) + word(p)
    cost = price(fork, 0x05, data)
    assert run(fork, 0x05, data, cost) == word(pow(3, p - 2, p))
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x05, data, cost - 1)


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


@pytest.mark.parametrize("fork", since("istanbul"))
def test_blake2f(fork: str) -> None:
    # With 12 rounds and the final flag, F on the one block of "abc" is the whole BLAKE2b-512 hash.
    data = blake2f_input(12, b"abc", 1)
    assert run(fork, 0x09, data, 12) == hashlib.blake2b(b"abc").digest()
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x09, data, 11)


@pytest.mark.parametrize("fork", since("istanbul"))
def test_blake2f_order_of_checks(fork: str) -> None:
    # The length is checked before the gas, and the gas before the flag.
    with pytest.raises(ValueError, match="invalidLength"):
        run(fork, 0x09, blake2f_input(12, b"abc", 1)[:-1], 0)
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x09, blake2f_input(12, b"abc", 2), 11)
    with pytest.raises(ValueError, match="invalidFlag"):
        run(fork, 0x09, blake2f_input(12, b"abc", 2), 12)


@pytest.mark.parametrize("address, size, cost, out_size", [
    # The sum of two points at infinity is the point at infinity.
    (0x0B, 256, 375, 128),
    (0x0D, 512, 600, 256),
])
@pytest.mark.parametrize("fork", since("pectra"))
def test_bls12_add_infinity(fork: str, address: int, size: int, cost: int, out_size: int) -> None:
    assert run(fork, address, bytes(size), cost) == bytes(out_size)
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, address, bytes(size), cost - 1)


@pytest.mark.parametrize("address, size, cost, out_size", [
    (0x10, 64, 5500, 128),
    (0x11, 128, 23800, 256),
])
@pytest.mark.parametrize("fork", since("pectra"))
def test_bls12_map_zero(fork: str, address: int, size: int, cost: int, out_size: int) -> None:
    # The zero field element maps to a point, which the EIP-2537 vectors fix.
    assert len(run(fork, address, bytes(size), cost)) == out_size
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, address, bytes(size), cost - 1)
