"""The checks of AccountRange and StorageRanges answers, built from reference tries."""

# The answers follow caps/snap.md of ethereum/devp2p at commit 88f1c808, which EthLib cites.
# The reference trie in `trie_reference.py` builds each root and proof apart from EthLib.

import pytest

from ethlib.cryptography import keccak
from ethlib.errors import SnapError
from ethlib.execution import trie
from ethlib.execution.network.snap import verify_account_range, verify_storage_ranges
from ethlib.serialization import rlp
from raising import raises
from trie_reference import Trie

EMPTY_ROOT = keccak.keccak256(b"\x80")
EMPTY_CODE = keccak.keccak256(b"")
ZERO = bytes(32)


def _scalar(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


# Every third account has storage and code, and the others are plain.
HASHES = sorted(keccak.keccak256(bytes([n])) for n in range(60))
FULL = {
    h: (
        _scalar(i + 1),
        _scalar(10 * i),
        h if i % 3 == 0 else EMPTY_ROOT,
        h if i % 3 == 0 else EMPTY_CODE,
    )
    for i, h in enumerate(HASHES)
}


def _slim(fields: tuple[bytes, bytes, bytes, bytes]) -> bytes:
    """The slim body: the empty root and the empty code hash become empty strings."""
    nonce, balance, root, code = fields
    root = b"" if root == EMPTY_ROOT else root
    code = b"" if code == EMPTY_CODE else code
    return rlp.encode([nonce, balance, root, code])


STATE = Trie({h: rlp.encode(list(fields)) for h, fields in FULL.items()})


def _accounts(first: int, end: int) -> list[tuple[bytes, bytes]]:
    return [(h, _slim(FULL[h])) for h in HASHES[first:end]]


def _range_error(fault: str) -> str:
    return (
        "range answer does not verify: EthLib.Execution.Network.SnapRangeError.range "
        f"(EthLib.Execution.Trie.RangeError.{fault})"
    )


def test_whole_state() -> None:
    assert verify_account_range(STATE.root, ZERO, _accounts(0, 60), []) is False


def test_partial_range() -> None:
    accounts = _accounts(10, 30)
    proof = STATE.proof(HASHES[10]) + STATE.proof(HASHES[29])
    assert verify_account_range(STATE.root, HASHES[10], accounts, proof) is True


def test_empty_reply() -> None:
    assert verify_account_range(STATE.root, ZERO, [], []) is None


def test_no_account_after_the_start() -> None:
    top = b"\xff" * 32
    assert verify_account_range(STATE.root, top, [], STATE.proof(top)) is False


def test_rejects_a_full_body() -> None:
    # The account with storage has no empty field, so its full body is also its slim body.
    # A plain account must come in slim form.
    accounts = _accounts(0, 60)
    plain = HASHES[1]
    accounts[1] = (plain, rlp.encode(list(FULL[plain])))
    with raises(
        SnapError,
        "range answer does not verify: EthLib.Execution.Network.SnapRangeError.slimAccount",
    ) as error:
        verify_account_range(STATE.root, ZERO, accounts, [])
    assert error.value.code == 3


def test_rejects_a_gapped_account_range() -> None:
    accounts = _accounts(10, 30)
    proof = STATE.proof(HASHES[10]) + STATE.proof(HASHES[29])
    del accounts[7]
    with raises(SnapError, _range_error("mismatch")) as error:
        verify_account_range(STATE.root, HASHES[10], accounts, proof)
    assert error.value.code == 207


# The storage of three accounts: slot hashes and their values in the storage trie.
STORAGES = [
    {keccak.keccak256(bytes([a, n])): rlp.encode(_scalar(n + 1)) for n in range(size)}
    for a, size in enumerate([5, 1, 40])
]
STORAGE_TRIES = [Trie(slots) for slots in STORAGES]
ROOTS = [t.root for t in STORAGE_TRIES]


def _slots(account: int, first: int = 0, end: int | None = None) -> list[tuple[bytes, bytes]]:
    keys = sorted(STORAGES[account])[first:end]
    return [(key, STORAGES[account][key]) for key in keys]


def test_whole_storage_of_each_account() -> None:
    slots = [_slots(0), _slots(1), _slots(2)]
    assert verify_storage_ranges(ROOTS, b"", slots, []) is False


def test_last_range_cut_short() -> None:
    # Every range but the last is whole, and the proof covers the last from the zero hash.
    last = _slots(2, 0, 25)
    proof = STORAGE_TRIES[2].proof(ZERO) + STORAGE_TRIES[2].proof(last[-1][0])
    assert verify_storage_ranges(ROOTS, b"", [_slots(0), _slots(1), last], proof) is True


def test_fewer_ranges_than_accounts() -> None:
    assert verify_storage_ranges(ROOTS, b"", [_slots(0)], []) is False


def test_one_account_from_a_start() -> None:
    keys = sorted(STORAGES[2])
    last = _slots(2, 10, 30)
    proof = STORAGE_TRIES[2].proof(keys[10]) + STORAGE_TRIES[2].proof(last[-1][0])
    assert verify_storage_ranges(ROOTS[2:], keys[10], [last], proof) is True


def test_proof_without_range() -> None:
    # No slot from the start on: the proof alone shows it, for the one requested account.
    top = b"\xff" * 32
    assert verify_storage_ranges(ROOTS[2:], top, [], STORAGE_TRIES[2].proof(top)) is False


def test_empty_storage_reply() -> None:
    assert verify_storage_ranges(ROOTS, b"", [], []) is None


def test_rejects_a_cut_range_before_the_last() -> None:
    # Only the last range may stop short, so the first range is checked as its whole trie and fails.
    with raises(SnapError, _range_error("mismatch")):
        verify_storage_ranges(ROOTS, b"", [_slots(0, 0, 4), _slots(1)], [])


def test_rejects_more_ranges_than_accounts() -> None:
    with raises(
        SnapError,
        "range answer does not verify: EthLib.Execution.Network.SnapRangeError.tooManyRanges",
    ) as error:
        verify_storage_ranges(ROOTS[:1], b"", [_slots(0), _slots(1)], [])
    assert error.value.code == 4


@pytest.mark.parametrize("start", [b"\x00", bytes(31), bytes(33)])
def test_rejects_a_start_of_another_size(start: bytes) -> None:
    with raises(SnapError, f"bad start size: {len(start)}, expected 0 or 32"):
        verify_storage_ranges(ROOTS, start, [_slots(0)], [])


@pytest.mark.parametrize("index", range(3))
def test_reference_storage_roots(index: int) -> None:
    assert ROOTS[index] == trie.root(list(STORAGES[index].items()))


def test_reference_state_root() -> None:
    assert STATE.root == trie.root([(h, rlp.encode(list(f))) for h, f in FULL.items()])


def test_start_ignored_with_several_accounts() -> None:
    # Each range starts at the zero hash, so the proof of the last range starts there too.
    keys = sorted(STORAGES[2])
    last = _slots(2, 0, 25)
    proof = STORAGE_TRIES[2].proof(ZERO) + STORAGE_TRIES[2].proof(last[-1][0])
    assert verify_storage_ranges(ROOTS, keys[10], [_slots(0), _slots(1), last], proof) is True


def test_empty_storage_of_an_account() -> None:
    empty = Trie({})
    assert empty.root == EMPTY_ROOT
    roots = [ROOTS[0], EMPTY_ROOT, ROOTS[2]]
    assert verify_storage_ranges(roots, b"", [_slots(0), [], _slots(2)], []) is False


@pytest.mark.parametrize(
    ("root", "start", "message"),
    [
        (STATE.root[:31], ZERO, "expected 32 bytes, got 31"),
        (STATE.root, ZERO + b"\x00", "expected 32 bytes, got 33"),
    ],
)
def test_rejects_a_root_or_start_of_another_size(root: bytes, start: bytes, message: str) -> None:
    with raises(SnapError, message) as error:
        verify_account_range(root, start, _accounts(0, 60), [])
    assert error.value.code == 0
