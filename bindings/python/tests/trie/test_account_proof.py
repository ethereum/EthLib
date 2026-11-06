"""The check of whole `eth_getProof` answers of ethereum/execution-apis against a state root."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.errors import TrieError
from ethlib.execution import trie
from ethlib.serialization import rlp
from raising import raises

# `getproof/README.md` gives the origin of the files and their licence.

_DIRECTORY = Path(__file__).resolve().parent / "getproof"
_FILES = sorted(_DIRECTORY.glob("*.io"))

# The state root of block 60 of `tests/chain.rlp`, from which every account proof starts.
STATE_ROOT = bytes.fromhex("a6bd32516beae9780a8c90563bb28c18f4299855f3f9d7c1de2db9a609ce63ec")


def _answer(path: Path) -> dict:
    # The response is the line after `<< `.
    return next(
        json.loads(line[3:])["result"]
        for line in path.read_text().splitlines()
        if line.startswith("<< ")
    )


_WITH_STORAGE = _answer(_DIRECTORY / "get-account-proof-with-storage.io")


@pytest.mark.parametrize("path", _FILES, ids=lambda path: path.stem)
def test_answer_holds(path: Path) -> None:
    """Each answer of the vectors holds, with its account present and each slot set."""
    answer = _answer(path)
    assert trie.verify_account_proof(STATE_ROOT, answer) == [True] * len(answer["storageProof"])


def test_wrong_balance() -> None:
    """A balance other than that of the proven account does not hold."""
    answer = dict(_WITH_STORAGE, balance="0x6c")
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.accountMismatch"
    ):
        trie.verify_account_proof(STATE_ROOT, answer)


def test_wrong_storage_hash() -> None:
    """A storage root other than that of the proven account does not hold."""
    answer = dict(_WITH_STORAGE, storageHash="0x" + "00" * 32)
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.accountMismatch"
    ):
        trie.verify_account_proof(STATE_ROOT, answer)


def test_wrong_slot_value() -> None:
    """A word other than that of the proven slot does not hold, with the index of the slot."""
    slot = dict(_WITH_STORAGE["storageProof"][0], value="0x34")
    answer = dict(_WITH_STORAGE, storageProof=[slot])
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.slotMismatch 0"
    ):
        trie.verify_account_proof(STATE_ROOT, answer)


def test_absent_slot() -> None:
    """A slot whose proof shows it is not set is absent, and its value is not judged."""
    # The path of slot 6 leaves the storage trie at the root node, an empty child of its branch.
    root_node = _WITH_STORAGE["storageProof"][0]["proof"][0]
    slot = {"key": "0x6", "value": "0x5", "proof": [root_node]}
    answer = dict(_WITH_STORAGE, storageProof=[_WITH_STORAGE["storageProof"][0], slot])
    assert trie.verify_account_proof(STATE_ROOT, answer) == [True, False]


def test_slot_proof_fails() -> None:
    """A slot proof that does not reach the slot fails with the index of the slot."""
    # The root node alone does not reach the leaf of slot 0.
    root_node = _WITH_STORAGE["storageProof"][0]["proof"][0]
    slot = dict(_WITH_STORAGE["storageProof"][0], proof=[root_node])
    with raises(
        TrieError,
        "answer does not hold: EthLib.Execution.State.AccountProofError.slot 0 "
        "(EthLib.Execution.Trie.ProofError.missingNode)",
    ):
        trie.verify_account_proof(STATE_ROOT, dict(_WITH_STORAGE, storageProof=[slot]))


def test_absent_account() -> None:
    """The proof of an empty state shows every address absent, and no field is judged."""
    # The empty trie has the root keccak256(0x80), and its one node is the empty string 0x80.
    empty_root = keccak256(rlp.encode(b""))
    answer = dict(
        _WITH_STORAGE,
        accountProof=["0x80"],
        balance="0x1",
        storageProof=[],
    )
    assert trie.verify_account_proof(empty_root, answer) is None


def test_wrong_root() -> None:
    """An account proof that does not start from the state root does not hold."""
    with raises(
        TrieError,
        "answer does not hold: EthLib.Execution.State.AccountProofError.account "
        "(EthLib.Execution.Trie.ProofError.hashMismatch)",
    ) as error:
        trie.verify_account_proof(bytes(32), _WITH_STORAGE)
    assert error.value.code == 501


def test_field_pattern() -> None:
    """A nonce with a leading zero does not match the type `uint64` of execution-apis."""
    with raises(ValueError, "not a value of uint64: '0x00'"):
        trie.verify_account_proof(STATE_ROOT, dict(_WITH_STORAGE, nonce="0x00"))


def test_short_root() -> None:
    with raises(TrieError, "bad root size: 31, expected 32"):
        trie.verify_account_proof(STATE_ROOT[:31], _WITH_STORAGE)
