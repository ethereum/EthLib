"""Known answers of the RIPEMD-160 precompile.

The messages and digests are the test vectors on Bosselaers' RIPEMD-160 page,
https://homes.esat.kuleuven.be/~bosselae/ripemd160.html.
The precompile left-pads each 20-byte digest with twelve zero bytes.
"""

import pytest

from ethlib.precompiles import ripemd160 as precompile

VECTORS = [
    (b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
    (b"a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
    (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
    (b"message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
    (b"abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
    (
        b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "12a053384a9c0c88e405a06c27dcf49ada62eb2b",
    ),
    (
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
        "b0e20b6e3116640286ed3a87a5713079b21f5189",
    ),
    (b"1234567890" * 8, "9b752e45573d4b39f4dbd3323cab82bf63326bfb"),
    # The page's last vector, which the Lean kernel proofs leave out.
    (b"a" * 1_000_000, "52783243c1697bdbe16d37f97f68f08325dc1528"),
]

# Digests of `a` repeated n times, for the lengths at which the padding changes
# its number of blocks. They agree between OpenSSL and Python's hashlib.
PADDING_VECTORS = [
    (55, "0d8a8c9063a48576a7c97e9f95253a6e53ff6765"),
    (56, "e72334b46c83cc70bef979e15453706c95b888be"),
    (63, "e640041293fe663b9bf3f8c21ffecac03819e6b2"),
    (64, "9dfb7d374ad924f3f88de96291c33e9abed53e32"),
    (119, "23e398ff2bac815aa1bbb57ca2a669c841872919"),
    (120, "c476770a6dae31fcee8d25efe6559a05c8024595"),
]


def test_output_size() -> None:
    assert precompile.RIPEMD160_OUTPUT_BYTES == 32


@pytest.mark.parametrize("data, digest", VECTORS)
def test_paper_vectors(data: bytes, digest: str) -> None:
    assert precompile.ripemd160(data) == bytes(12) + bytes.fromhex(digest)


@pytest.mark.parametrize("count, digest", PADDING_VECTORS)
def test_padding_boundaries(count: int, digest: str) -> None:
    assert precompile.ripemd160(b"a" * count) == bytes(12) + bytes.fromhex(digest)


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        precompile.ripemd160("abc")  # type: ignore[arg-type]
