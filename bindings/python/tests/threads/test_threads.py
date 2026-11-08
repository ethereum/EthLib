"""Exports called from several threads at once, with or without the GIL."""

import sys
import sysconfig
import threading
from collections.abc import Callable

import pytest

from ethlib.cryptography import _native, bls, crc32, ethash, keccak
from ethlib.errors import BlsError
from ethlib.serialization import rlp

THREADS = 8
ROUNDS = 200

FREE_THREADED = bool(sysconfig.get_config_var("Py_GIL_DISABLED"))


def run_together(work: Callable[[int], object]) -> list[object]:
    """The result of `work(i)` for each thread `i`, with every thread started at once."""
    # The timeout breaks the barrier if a thread never reaches it, so the test fails, not hangs.
    barrier = threading.Barrier(THREADS, timeout=60)
    results: list[object] = [None] * THREADS
    errors: list[BaseException] = []

    def target(i: int) -> None:
        # Any failure, assertions too, goes to the main thread, which raises it again.
        try:
            barrier.wait()
            results[i] = work(i)
        except BaseException as error:
            errors.append(error)

    threads = [threading.Thread(target=target, args=(i,)) for i in range(THREADS)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    if errors:
        raise errors[0]
    return results


@pytest.mark.skipif(not FREE_THREADED, reason="only a free-threaded build can run without the GIL")
def test_import_leaves_the_gil_disabled() -> None:
    # The module is imported by now, and it declares that it needs no GIL.
    # ty reads the standard library of Python 3.12, which has no `sys._is_gil_enabled`.
    assert not sys._is_gil_enabled()  # ty: ignore[unresolved-attribute]


def test_same_results_from_every_thread() -> None:
    # Each thread runs a mix of exports, and gets the results that one thread alone gets.
    def work(i: int) -> list[object]:
        data = bytes([i]) * 64
        out: list[object] = []
        for n in range(ROUNDS):
            out.append(keccak.keccak256(data + bytes([n % 256])))
            out.append(crc32.crc32(data))
            out.append(rlp.decode(rlp.encode([data, [bytes([n % 256])]])))
            out.append(_native.pyvalue_echo({"n": n, "items": [data, (i, None)]}))
        out.append(ethash.cache_size(30000 * i))
        return out

    alone = [work(i) for i in range(THREADS)]
    assert run_together(work) == alone


# The tests below change a list while other threads read it.
# They catch a read in place only without the GIL, and on a build with it they run as smoke tests.


def test_list_that_another_thread_changes() -> None:
    # Half the threads encode one shared list while the others change it.
    # Each encoding reads a snapshot of the list, so it decodes to a list of the items it held.
    shared: list[bytes] = [b"x" * 32] * 16

    def work(i: int) -> int:
        if i % 2 == 0:
            for n in range(ROUNDS):
                shared.append(bytes([n % 256]) * 32)
                del shared[: len(shared) // 2]
            return 0
        for _ in range(ROUNDS):
            decoded = rlp.decode(rlp.encode(shared))
            assert all(isinstance(item, bytes) and len(item) == 32 for item in decoded)
        return 1

    assert run_together(work) == [i % 2 for i in range(THREADS)]


def test_typed_list_that_another_thread_changes() -> None:
    # The generic converter copies a list before it reads it, so a shared list is safe there too.
    shared: list[object] = [1, b"a", None] * 8

    def work(i: int) -> int:
        if i % 2 == 0:
            for n in range(ROUNDS):
                shared.append(n)
                del shared[: len(shared) // 2]
            return 0
        for _ in range(ROUNDS):
            echoed = _native.pyvalue_echo(shared)
            assert isinstance(echoed, list)
        return 1

    assert run_together(work) == [i % 2 for i in range(THREADS)]


def test_sequence_of_bytes_that_another_thread_changes() -> None:
    # The readers of a sequence of bytes, such as BLS aggregation, take a snapshot.
    # Each aggregation reads whole signatures, or none when it finds the list empty.
    signature = bls.sign(bls.key_gen(bytes(32)), b"message")
    shared: list[bytes] = [signature] * 4

    def work(i: int) -> int:
        if i % 2 == 0:
            for _ in range(ROUNDS):
                shared.append(signature)
                del shared[: len(shared) // 2]
            return 0
        for _ in range(ROUNDS // 10):
            try:
                assert len(bls.aggregate(shared)) == len(signature)
            except BlsError as error:
                assert str(error) == "empty signature list"
        return 1

    assert run_together(work) == [i % 2 for i in range(THREADS)]
