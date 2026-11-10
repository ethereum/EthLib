"""The range check of a trie, against ranges and proofs that a reference trie builds."""

# Each key is the Keccak-256 hash of one byte, so the paths spread over the whole trie.
# The reference trie in `trie_reference.py` builds the root and the proofs apart from EthLib.

import pytest

from ethlib.cryptography import keccak
from ethlib.errors import TrieError
from ethlib.execution import trie
from raising import raises
from trie_reference import Trie

KEYS = sorted(keccak.keccak256(bytes([n])) for n in range(200))
PAIRS = {key: b"\x01" + key[:3] for key in KEYS}
TRIE = Trie(PAIRS)
ZERO = bytes(32)
TOP = b"\xff" * 32


def _range(first: int, end: int) -> list[tuple[bytes, bytes]]:
    """The entries of the keys from index `first` up to `end`, excluded."""
    return [(key, PAIRS[key]) for key in KEYS[first:end]]


def _proof(start: bytes, entries: list[tuple[bytes, bytes]]) -> list[bytes]:
    """The boundary proofs of a range: the path of its start and the path of its last key."""
    return TRIE.proof(start) + (TRIE.proof(entries[-1][0]) if entries else [])


def _check(start: bytes, entries: list[tuple[bytes, bytes]]) -> bool:
    return trie.verify_range(TRIE.root, start, entries, _proof(start, entries))


def _fault(name: str) -> str:
    """The message of a range that fails with the error `name`."""
    return f"range does not verify: EthLib.Execution.Trie.RangeError.{name}"


def test_reference_root() -> None:
    # The reference trie and EthLib agree on the root of the keys.
    assert TRIE.root == trie.root(list(PAIRS.items()))


def test_whole_trie_without_proof() -> None:
    assert trie.verify_range(TRIE.root, ZERO, _range(0, 200), []) is False


@pytest.mark.parametrize(
    ("first", "end", "more"),
    [(0, 50, True), (0, 200, False), (37, 120, True), (150, 200, False), (0, 1, True)],
)
def test_ranges_from_a_key(first: int, end: int, more: bool) -> None:
    start = ZERO if first == 0 else KEYS[first]
    assert _check(start, _range(first, end)) is more


def test_start_between_two_keys() -> None:
    # A start that the trie does not hold, just above the key before the range.
    start = (int.from_bytes(KEYS[36], "big") + 1).to_bytes(32, "big")
    assert _check(start, _range(37, 120)) is True


def test_last_key_alone() -> None:
    assert _check(KEYS[199], _range(199, 200)) is False


def test_nothing_after_the_start() -> None:
    assert _check(TOP, []) is False


def test_rejects_an_empty_range_before_keys() -> None:
    # Keys remain after the start, so an empty range hides them.
    with raises(TrieError, _fault("mismatch")):
        _check(KEYS[150], [])


def test_rejects_a_gap() -> None:
    entries = _range(37, 120)
    del entries[40]
    with raises(TrieError, _fault("mismatch")) as error:
        trie.verify_range(TRIE.root, KEYS[37], entries, _proof(KEYS[37], _range(37, 120)))
    assert error.value.code == 207


def test_rejects_a_skipped_first_key() -> None:
    # The range starts one key late, so the key at the start is missing.
    entries = _range(38, 120)
    with raises(TrieError, _fault("mismatch")):
        trie.verify_range(TRIE.root, KEYS[37], entries, _proof(KEYS[37], entries))


def test_rejects_an_invented_key() -> None:
    entries = _range(37, 120)
    invented = (int.from_bytes(KEYS[60], "big") + 1).to_bytes(32, "big")
    entries.insert(24, (invented, b"\x01"))
    with raises(TrieError, _fault("mismatch")):
        trie.verify_range(TRIE.root, KEYS[37], entries, _proof(KEYS[37], entries))


def test_rejects_a_changed_value() -> None:
    entries = _range(37, 120)
    entries[10] = (entries[10][0], b"\x02")
    with raises(TrieError, _fault("mismatch")):
        _check(KEYS[37], entries)


def test_rejects_a_partial_range_without_proof() -> None:
    with raises(TrieError, _fault("mismatch")):
        trie.verify_range(TRIE.root, ZERO, _range(0, 199), [])


def test_rejects_reordered_keys() -> None:
    entries = _range(37, 120)
    entries[3], entries[4] = entries[4], entries[3]
    with raises(TrieError, _fault("unsorted")) as error:
        _check(KEYS[37], entries)
    assert error.value.code == 201


def test_rejects_a_key_below_the_start() -> None:
    with raises(TrieError, _fault("beforeStart")) as error:
        _check(KEYS[38], _range(37, 120))
    assert error.value.code == 202


def test_rejects_an_empty_value() -> None:
    entries = _range(37, 120)
    entries[5] = (entries[5][0], b"")
    with raises(TrieError, _fault("emptyValue")) as error:
        _check(KEYS[37], entries)
    assert error.value.code == 203


def test_rejects_a_missing_proof_node() -> None:
    # Only the root node: the walk down the two paths lacks the next node.
    entries = _range(37, 120)
    with raises(
        TrieError,
        "range does not verify: EthLib.Execution.Trie.RangeError.proof "
        "(EthLib.Execution.Trie.ProofError.missingNode)",
    ) as error:
        trie.verify_range(TRIE.root, KEYS[37], entries, TRIE.proof(KEYS[37])[:1])
    assert error.value.code == 204


def test_ignores_repeated_proof_nodes() -> None:
    # The two boundary proofs share their upper nodes, so a sender may list them twice.
    entries = _range(37, 120)
    proof = _proof(KEYS[37], entries)
    assert trie.verify_range(TRIE.root, KEYS[37], entries, proof + proof) is True


def test_rejects_a_short_root() -> None:
    with raises(TrieError, "expected 32 bytes, got 31"):
        trie.verify_range(TRIE.root[:31], ZERO, _range(0, 200), [])


# Sixteen keys that share 30 bytes, and one far key.
# Their leaves encode in under 32 bytes, so each sits inside its parent and no proof lists it.
CLOSE = sorted([bytes(30) + bytes([n, 1]) for n in range(16)] + [TOP])
CLOSE_PAIRS = {key: b"\x01" for key in CLOSE}
CLOSE_TRIE = Trie(CLOSE_PAIRS)


def test_reference_root_of_inline_nodes() -> None:
    assert CLOSE_TRIE.root == trie.root(list(CLOSE_PAIRS.items()))


def test_range_over_inline_nodes() -> None:
    entries = [(key, b"\x01") for key in CLOSE[3:12]]
    proof = CLOSE_TRIE.proof(CLOSE[3]) + CLOSE_TRIE.proof(CLOSE[11])
    assert trie.verify_range(CLOSE_TRIE.root, CLOSE[3], entries, proof) is True


def test_rejects_a_changed_inline_value() -> None:
    entries = [(key, b"\x01") for key in CLOSE[3:12]]
    proof = CLOSE_TRIE.proof(CLOSE[3]) + CLOSE_TRIE.proof(CLOSE[11])
    entries[4] = (entries[4][0], b"\x02")
    with raises(TrieError, _fault("mismatch")):
        trie.verify_range(CLOSE_TRIE.root, CLOSE[3], entries, proof)
