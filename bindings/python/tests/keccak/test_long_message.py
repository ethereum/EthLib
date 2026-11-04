"""Keccak-256 and Keccak-512 of a 64 MiB message, which once overflowed the stack."""

from ethlib.cryptography import keccak

# 64 MiB and 7 bytes, so the message ends inside a block of either rate.
MESSAGE = (bytes(range(256)) * ((64 << 20) // 256 + 1))[: (64 << 20) + 7]

# Both digests were computed with pycryptodome 3.23.0.
DIGEST_256 = bytes.fromhex("a3238107136a7c44ed9488d248b58a01c044355252f3494153da4b549f302289")
DIGEST_512 = bytes.fromhex(
    "0ae3f1f3ee35944052f8bb17c2750ac284b15f96b326ff4abcb088f157a27285"
    "38e80b52b184cf199ffd7e9a3e1f576104a057403d1cb2f04a202413d102e20f"
)


def test_keccak256_long_message() -> None:
    assert keccak.keccak256(MESSAGE) == DIGEST_256


def test_keccak512_long_message() -> None:
    assert keccak.keccak512(MESSAGE) == DIGEST_512
