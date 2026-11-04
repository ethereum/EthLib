"""AES-CTR on 4 MiB of data, which once overflowed the stack."""

from ethlib.cryptography import aes

KEY = bytes(range(16))
# The counter wraps from 2^128 - 1 to 0 at the second block.
INITIAL_COUNTER = b"\xff" * 16
BLOCKS = (4 << 20) // 16


def test_ctr_long_message() -> None:
    # On zero data, block j of the output is the cipher of counter j.
    out = aes.ctr(KEY, INITIAL_COUNTER, bytes(16 * BLOCKS))
    assert len(out) == 16 * BLOCKS
    for j in (0, 1, BLOCKS - 1):
        counter = (int.from_bytes(INITIAL_COUNTER, "big") + j) % (1 << 128)
        expected = aes.encrypt_block(KEY, counter.to_bytes(16, "big"))
        assert out[16 * j : 16 * j + 16] == expected
