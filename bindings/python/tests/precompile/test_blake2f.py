"""The BLAKE2F precompile against the test vectors of EIP-152 and of BLAKE2.

The EIP-152 vectors are copied byte for byte.

File: EIPS/eip-152.md
Repository: ethereum/EIPs
Commit: 0ce679f4654ba4d120c97113626f320475e22fa9
"""

import hashlib
import struct

import pytest

from ethlib.precompiles import run

from .forks import ends

# The fork that adds the precompile, istanbul, and the latest fork: no fork in between changes it.
FORKS = ends("istanbul")

ADDRESS = 0x09

# The 208 bytes that every nonempty EIP-152 vector shares, after its rounds field:
# h, then m ("abc" and 125 zero bytes), then t0 = 3 and t1 = 0.
SHARED = (
    "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b"
    "616263" + "00" * 125 + "0300000000000000" + "0000000000000000"
)


def vector(rounds: str, flag: str) -> bytes:
    """The input of an EIP-152 vector: its rounds field, the shared bytes, then its flag."""
    return bytes.fromhex(rounds + SHARED + flag)


# Test vectors 0 to 3: the inputs the precompile rejects, with the error it names.
REJECTED = [
    (b"", "invalidInputLength"),
    (vector("00000c", "01"), "invalidInputLength"),
    (vector("000000000c", "01"), "invalidInputLength"),
    (vector("0000000c", "02"), "invalidFlag"),
]

# Test vectors 4 to 7: the rounds field, the flag and the output.
ACCEPTED = [
    ("00000000", "01",
     "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
     "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b"),
    ("0000000c", "01",
     "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
     "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"),
    ("0000000c", "00",
     "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752"
     "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735"),
    ("00000001", "01",
     "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb"
     "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421"),
]


@pytest.mark.parametrize("data, error", REJECTED)
@pytest.mark.parametrize("fork", FORKS)
def test_eip152_rejected(fork: str, data: bytes, error: str) -> None:
    with pytest.raises(ValueError, match=error):
        run(fork, ADDRESS, data, 12)


@pytest.mark.parametrize("rounds, flag, output", ACCEPTED)
@pytest.mark.parametrize("fork", FORKS)
def test_eip152_accepted(fork: str, rounds: str, flag: str, output: str) -> None:
    assert run(fork, ADDRESS, vector(rounds, flag), int(rounds, 16)) == bytes.fromhex(output)


@pytest.mark.parametrize("fork", FORKS)
def test_eip152_vector8_rounds(fork: str) -> None:
    # Test vector 8 asks for 2^32 - 1 rounds, too many to run in a test.
    # One unit of gas short of that count, the call fails before any round.
    # So the rounds field reads as 2^32 - 1, big-endian.
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, ADDRESS, vector("ffffffff", "01"), 2**32 - 2)


# The rest leave the EIP-152 layout: they build h, m, t0 and t1 themselves.

IV = [
    0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
    0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179,
]

SIGMA = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
]

MASK = 2**64 - 1


def rotr(x: int, n: int) -> int:
    return ((x >> n) | (x << (64 - n))) & MASK


def compress(rounds: int, h: list[int], m: list[int], t0: int, t1: int, final: bool) -> list[int]:
    """F of RFC 7693 §3.2, an oracle independent of the Lean code."""
    v = h + IV
    v[12] ^= t0
    v[13] ^= t1
    if final:
        v[14] ^= MASK

    def mix(a: int, b: int, c: int, d: int, x: int, y: int) -> None:
        # G of RFC 7693 §3.1.
        v[a] = (v[a] + v[b] + x) & MASK
        v[d] = rotr(v[d] ^ v[a], 32)
        v[c] = (v[c] + v[d]) & MASK
        v[b] = rotr(v[b] ^ v[c], 24)
        v[a] = (v[a] + v[b] + y) & MASK
        v[d] = rotr(v[d] ^ v[a], 16)
        v[c] = (v[c] + v[d]) & MASK
        v[b] = rotr(v[b] ^ v[c], 63)

    for i in range(rounds):
        s = SIGMA[i % 10]
        mix(0, 4, 8, 12, m[s[0]], m[s[1]])
        mix(1, 5, 9, 13, m[s[2]], m[s[3]])
        mix(2, 6, 10, 14, m[s[4]], m[s[5]])
        mix(3, 7, 11, 15, m[s[6]], m[s[7]])
        mix(0, 5, 10, 15, m[s[8]], m[s[9]])
        mix(1, 6, 11, 12, m[s[10]], m[s[11]])
        mix(2, 7, 8, 13, m[s[12]], m[s[13]])
        mix(3, 4, 9, 14, m[s[14]], m[s[15]])
    return [h[i] ^ v[i] ^ v[i + 8] for i in range(8)]


# The IV with the parameter block of RFC 7693 §2.5: a 64-byte digest, no key.
H = [IV[0] ^ 0x01010040] + IV[1:]


def encode(rounds: int, block: bytes, t0: int, t1: int, final: int) -> bytes:
    """The 213-byte input: rounds big-endian, then h, m, t0 and t1 little-endian, then the flag."""
    return (struct.pack(">I", rounds) + struct.pack("<8Q", *H) + block
            + struct.pack("<2Q", t0, t1) + bytes([final]))


def test_oracle_agrees_with_eip152() -> None:
    # The oracle gives the outputs of test vectors 4 to 7, so it is a fair judge below.
    m = list(struct.unpack("<16Q", b"abc".ljust(128, b"\0")))
    for rounds, flag, output in ACCEPTED:
        words = compress(int(rounds, 16), H, m, 3, 0, flag == "01")
        assert struct.pack("<8Q", *words) == bytes.fromhex(output)


@pytest.mark.parametrize("fork", FORKS)
def test_full_block(fork: str) -> None:
    # The unkeyed BLAKE2b-512 digest of the 128 bytes 0x00 to 0x7f.
    # Every word of m differs.
    #
    # File: testvectors/blake2-kat.json
    # Repository: BLAKE2/BLAKE2
    # Commit: ed1974ea83433eba7b2d95c5dcd9ac33cb847913
    block = bytes(range(128))
    digest = bytes.fromhex(
        "2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e"
        "8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115")
    assert hashlib.blake2b(block).digest() == digest
    assert run(fork, ADDRESS, encode(12, block, 128, 0, 1), 12) == digest


@pytest.mark.parametrize("fork", FORKS)
def test_high_offset(fork: str) -> None:
    # Test vector 5 with t1 = 1, the high word of the offset counter.
    # A hash sets t1 only past 2^64 bytes, so no hash vector pins it.
    block = b"abc".ljust(128, b"\0")
    expected = bytes.fromhex(
        "5811650d30e41b4e9641ddb368e6b697ac38f34598f74e9f253db772f522fa80"
        "55e373dcd96b59e0e30efa21ed0c4110eeb8dc7a33d626ec6a2930a1808a5560")
    m = list(struct.unpack("<16Q", block))
    assert struct.pack("<8Q", *compress(12, H, m, 3, 1, True)) == expected
    assert run(fork, ADDRESS, encode(12, block, 3, 1, 1), 12) == expected
