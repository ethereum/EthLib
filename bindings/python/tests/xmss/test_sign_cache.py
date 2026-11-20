"""Signing gives the same bytes on every call, whatever secret keys the extension keeps."""

import threading
import time
from collections.abc import Callable

import pytest

from ethlib.cryptography import xmss

from . import fixtures

# The extension keeps the secret keys of the last few seeds, which only the time of a call shows.
# A seed it does not keep builds the top tree and a bottom tree, each costing a key generation.
# A signature in a bottom tree it keeps makes one one-time signature.

# The number of seeds the extension keeps: update it with `XMSS_KEY_CACHE_SEEDS` in `xmss.c`.
CACHE_SEEDS = 2

SEED = fixtures.SEED_KNOWN_ANSWER
MESSAGE = fixtures.MESSAGE_KNOWN_ANSWER
PUBLIC_KEY = fixtures.read_output("key_gen", "key_gen_known_answer")

# The size of a bottom tree, in leaf indices.
TREE_SIZE = 1 << xmss.LAYER_HEIGHT


def near_seed(tag: int, *, first: bool = False) -> bytes:
    """A seed that differs from SEED in its last byte only, or in its first byte only."""
    if first:
        return bytes([SEED[0] ^ tag]) + SEED[1:]
    return SEED[:-1] + bytes([SEED[-1] ^ tag])


def timed_sign(seed: bytes, leaf_index: int) -> tuple[float, bytes]:
    """The time a signature takes, and the signature."""
    start = time.perf_counter()
    signature = xmss.sign(seed, leaf_index, MESSAGE)
    return time.perf_counter() - start, signature


def run_threads(work: Callable[[int], bytes], count: int) -> list[bytes]:
    """The results of `work(i)` for i below `count`, each in its own thread, all started at once."""
    barrier = threading.Barrier(count, timeout=600)
    results: dict[int, bytes] = {}
    errors: list[BaseException] = []

    def run(i: int) -> None:
        try:
            barrier.wait()
            results[i] = work(i)
        except BaseException as error:
            errors.append(error)

    threads = [threading.Thread(target=run, args=(i,)) for i in range(count)]
    for thread in threads:
        thread.start()
    deadline = time.monotonic() + 1800
    for thread in threads:
        thread.join(timeout=max(0.0, deadline - time.monotonic()))
        assert not thread.is_alive()
    if errors:
        raise errors[0]
    return [results[i] for i in range(count)]


@pytest.mark.parametrize(
    ("leaf_index", "case"),
    [
        (fixtures.LEAF_FIRST, "sign_first_leaf"),
        (1, None),
        (fixtures.LEAF_SECOND_TREE, "sign_second_tree"),
        (TREE_SIZE + 5, None),
        (3 * TREE_SIZE, None),
    ],
    ids=["0", "1", "2^16", "2^16+5", "3*2^16"],
)
def test_repeated_signing(leaf_index: int, case: str | None) -> None:
    # The first call may build the trees; the next ones read them.
    first = xmss.sign(SEED, leaf_index, MESSAGE)
    again = [xmss.sign(SEED, leaf_index, MESSAGE) for _ in range(2)]
    assert again == [first, first]
    # The committed cases come from the signer that rebuilt every tree from the seed.
    if case is not None:
        assert first == fixtures.read_output("sign", case)
    assert xmss.signature_index(first) == leaf_index
    assert xmss.verify(PUBLIC_KEY, MESSAGE, first)


def test_eviction() -> None:
    # Seeds that differ from SEED in one byte, so a seed compared in part would be confused.
    others = [near_seed(tag) for tag in range(1, CACHE_SEEDS)]
    last = near_seed(1, first=True)
    # SEED with bottom tree 0 kept, then the other seeds: the cache is full.
    xmss.sign(SEED, 1, MESSAGE)
    public_keys = [xmss.key_gen(seed) for seed in others]
    warm, signature = timed_sign(SEED, fixtures.LEAF_FIRST)
    assert signature == fixtures.read_output("sign", "sign_first_leaf")
    # Using the other seeds again leaves SEED the least recently used.
    assert [xmss.key_gen(seed) for seed in others] == public_keys
    # One seed more evicts SEED, so its trees are built again, with the same bytes.
    # Only this test uses `last`, so it is not kept unless the test reruns in one process.
    public_keys.append(xmss.key_gen(last))
    cold, signature = timed_sign(SEED, fixtures.LEAF_FIRST)
    assert signature == fixtures.read_output("sign", "sign_first_leaf")
    # A tree costs 2^16 one-time keys, so a factor of 4 leaves room for noise.
    assert warm * 4 < cold
    # No near seed signs with the key of SEED or of another near seed.
    assert len(set(public_keys)) == CACHE_SEEDS
    assert PUBLIC_KEY not in public_keys
    signature = xmss.sign(last, 0, MESSAGE)
    assert xmss.verify(public_keys[-1], MESSAGE, signature)
    assert not xmss.verify(PUBLIC_KEY, MESSAGE, signature)


def test_kept_tree_is_faster() -> None:
    # Bottom tree 2 of SEED is used by this test only, so its first signature builds it.
    building, _ = timed_sign(SEED, 2 * TREE_SIZE)
    reading, _ = timed_sign(SEED, 2 * TREE_SIZE + 1)
    assert reading * 4 < building


def test_key_gen_keeps_signing_warm() -> None:
    # Key generation on a kept seed reads its public key, and keeps the bottom trees it holds.
    xmss.sign(SEED, 1, MESSAGE)
    before, _ = timed_sign(SEED, fixtures.LEAF_FIRST)
    assert xmss.key_gen(SEED) == PUBLIC_KEY
    after, signature = timed_sign(SEED, fixtures.LEAF_FIRST)
    assert signature == fixtures.read_output("sign", "sign_first_leaf")
    # Rebuilding bottom tree 0 would cost 2^16 one-time keys.
    assert after < max(4 * before, 1.0)


def test_threads_on_a_kept_key() -> None:
    # Eight threads share the kept key of SEED; without the GIL, they read it at once.
    # Two of them build a new bottom tree, so their stores free keys that the others still read.
    leaf_indices = [2 + i for i in range(6)] + [4 * TREE_SIZE, 5 * TREE_SIZE]
    xmss.sign(SEED, 1, MESSAGE)
    concurrent = run_threads(lambda i: xmss.sign(SEED, leaf_indices[i], MESSAGE), 8)
    serial = [xmss.sign(SEED, leaf_index, MESSAGE) for leaf_index in leaf_indices]
    assert concurrent == serial
    assert [xmss.signature_index(signature) for signature in serial] == leaf_indices
    assert all(xmss.verify(PUBLIC_KEY, MESSAGE, signature) for signature in serial)


def test_threads_on_cold_seeds() -> None:
    # Eight threads sign with two cold seeds, four per seed; without the GIL, they all build keys.
    # Key generation reads kept keys here, so the eviction test is the oracle for confused seeds.
    seeds = [near_seed(0x40), near_seed(0x41)]
    concurrent = run_threads(lambda i: xmss.sign(seeds[i % 2], i, MESSAGE), 8)
    serial = [xmss.sign(seeds[i % 2], i, MESSAGE) for i in range(8)]
    assert concurrent == serial
    assert [xmss.signature_index(signature) for signature in serial] == list(range(8))
    for i, seed in enumerate(seeds):
        public_key = xmss.key_gen(seed)
        assert all(xmss.verify(public_key, MESSAGE, signature) for signature in serial[i::2])
