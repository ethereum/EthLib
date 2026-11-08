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


def _with_unset_slot(value: str) -> dict:
    # The path of slot 6 leaves the storage trie at the root node, an empty child of its branch.
    root_node = _WITH_STORAGE["storageProof"][0]["proof"][0]
    slot = {"key": "0x6", "value": value, "proof": [root_node]}
    return dict(_WITH_STORAGE, storageProof=[_WITH_STORAGE["storageProof"][0], slot])


def test_absent_slot() -> None:
    """A slot whose proof shows it is not set is absent, with the value 0."""
    assert trie.verify_account_proof(STATE_ROOT, _with_unset_slot("0x0")) == [True, False]


def test_absent_slot_nonzero() -> None:
    """A slot that is not set holds 0, so another value does not hold."""
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.slotMismatch 1"
    ) as error:
        trie.verify_account_proof(STATE_ROOT, _with_unset_slot("0x5"))
    assert error.value.code == 506


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


# The empty trie has the root keccak256(0x80), and its one node is 0x80, the encoding of b"".
_EMPTY_ROOT = keccak256(rlp.encode(b""))

# The answer for an address without an account, against the empty state.
# Its hashes are those of an account with no code and no storage.
_ABSENT = {
    "address": _WITH_STORAGE["address"],
    "nonce": "0x0",
    "balance": "0x0",
    "codeHash": "0x" + keccak256(b"").hex(),
    "storageHash": "0x" + _EMPTY_ROOT.hex(),
    "accountProof": ["0x80"],
    "storageProof": [],
}


def test_absent_account() -> None:
    """An empty state shows the address absent, with the hashes of no code and no storage."""
    assert trie.verify_account_proof(_EMPTY_ROOT, _ABSENT) is None


@pytest.mark.parametrize(
    "zero_fields",
    [("codeHash", "storageHash"), ("codeHash",), ("storageHash",)],
    ids="+".join,
)
def test_absent_account_zero_hashes(zero_fields: tuple[str, ...]) -> None:
    """An absent account may give the zero hash for either hash, or both, judged apart."""
    answer = dict(_ABSENT, **dict.fromkeys(zero_fields, "0x" + "00" * 32))
    assert trie.verify_account_proof(_EMPTY_ROOT, answer) is None


@pytest.mark.parametrize("proof", [[], ["0x80"], ["0x01"]], ids=repr)
def test_absent_account_slot(proof: list[str]) -> None:
    """A slot of an absent account that gives the word 0 holds, whatever its proof."""
    slot = {"key": "0x1", "value": "0x0", "proof": proof}
    answer = dict(_ABSENT, storageProof=[slot])
    assert trie.verify_account_proof(_EMPTY_ROOT, answer) is None


def test_absent_account_slot_nonzero() -> None:
    """A slot of an absent account with a word other than 0 does not hold, with its index."""
    slots = [
        {"key": "0x1", "value": "0x0", "proof": []},
        {"key": "0x2", "value": "0x5", "proof": []},
    ]
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.slotMismatch 1"
    ) as error:
        trie.verify_account_proof(_EMPTY_ROOT, dict(_ABSENT, storageProof=slots))
    assert error.value.code == 506


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("nonce", "0x1"),
        ("balance", "0x1"),
        ("codeHash", "0x" + "11" * 32),
        ("storageHash", _WITH_STORAGE["storageHash"]),
        # The empty value of one hash is not a reading of the other.
        ("codeHash", "0x" + _EMPTY_ROOT.hex()),
        ("storageHash", "0x" + keccak256(b"").hex()),
    ],
)
def test_absent_account_field(field: str, value: str) -> None:
    """An absent account with a field that fits no reading of an absent account does not hold."""
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.accountMismatch"
    ) as error:
        trie.verify_account_proof(_EMPTY_ROOT, dict(_ABSENT, **{field: value}))
    assert error.value.code == 503


def test_absent_account_fields_before_slots() -> None:
    """The fields of an absent account are checked before its slots."""
    slot = {"key": "0x1", "value": "0x5", "proof": []}
    answer = dict(_ABSENT, balance="0x1", storageProof=[slot])
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.accountMismatch"
    ) as error:
        trie.verify_account_proof(_EMPTY_ROOT, answer)
    assert error.value.code == 503


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
    with raises(TrieError, "nonce: leading zero") as error:
        trie.verify_account_proof(STATE_ROOT, dict(_WITH_STORAGE, nonce="0x00"))
    assert error.value.code == 0


_SLOT = {"key": "0x0", "value": "0x0", "proof": []}


@pytest.mark.parametrize(
    ("change", "message"),
    [
        # A missing field, and a field of value null, which counts as absent.
        ({"address": None}, "answer: no field address"),
        ({"storageProof": "0x"}, "storageProof: not an array"),
        # The nonce is a uint64, so 2^64 is out of range.
        ({"nonce": "0x10000000000000000"}, "nonce: above 2^64"),
        # A hash and a proof node take lowercase hex digits only, two for each byte.
        ({"codeHash": "0x" + "AA" * 32}, "codeHash: not a hex digit"),
        ({"accountProof": ["0x123"]}, "accountProof: odd number of hex digits"),
        # A storage key has at most 64 lowercase digits behind its 0x marker.
        ({"storageProof": [dict(_SLOT, key="0x" + "1" * 65)]}, "key: more than 64 hex digits"),
        ({"storageProof": [dict(_SLOT, key="0xA")]}, "key: not a hex digit"),
        ({"storageProof": [dict(_SLOT, key="00")]}, "key: no 0x marker"),
    ],
)
def test_field_out_of_its_pattern(change: dict, message: str) -> None:
    """Lean reads each field of the answer in the pattern of its base type, before any check."""
    with raises(TrieError, message) as error:
        trie.verify_account_proof(STATE_ROOT, {**_WITH_STORAGE, **change})
    assert error.value.code == 0


def test_answer_is_an_object() -> None:
    with raises(TrieError, "answer: not an object") as error:
        trie.verify_account_proof(STATE_ROOT, [])  # ty: ignore[invalid-argument-type]
    assert error.value.code == 0


def test_uppercase_address() -> None:
    """An address may use uppercase hex digits, so the answer reads and holds as before."""
    answer = dict(_WITH_STORAGE, address=_WITH_STORAGE["address"].upper().replace("0X", "0x"))
    assert trie.verify_account_proof(STATE_ROOT, answer) == trie.verify_account_proof(
        STATE_ROOT, _WITH_STORAGE
    )


def test_short_root() -> None:
    with raises(TrieError, "bad root size: 31, expected 32"):
        trie.verify_account_proof(STATE_ROOT[:31], _WITH_STORAGE)


# The two proofs below are built by hand, with one leaf each.
# In each, the value under the key is not what the check reads.
#
# The leaf of an address is a list of two items: its path and its value.
# The path is 0x20 followed by the hash of the address.
# 0x20 is the leaf flag of the hex-prefix encoding.
# The hash then gives all 64 nibbles of the path.
_ADDRESS = "0x" + "11" * 20
_ZERO = "0x" + "00" * 32


def test_account_not_rlp() -> None:
    """A leaf whose value is not the RLP encoding of an account does not hold."""
    # Fixture: the value of the leaf is the string 0x01.
    # Why: 0x01 is an RLP item, but not the list of the four fields of an account.
    node = "e3a120e2c07404b8c1df4c46226425cac68c28d27a766bbddce62309f36724839b22c001"
    root = bytes.fromhex("474cd3297ebe904d4ec8b9a233561a8729f8f3c2994fb1e046346ed9ab3b647a")
    answer = {
        "address": _ADDRESS,
        "nonce": "0x0",
        "balance": "0x0",
        "codeHash": _ZERO,
        "storageHash": _ZERO,
        "accountProof": ["0x" + node],
        "storageProof": [],
    }
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.accountEncoding"
    ) as error:
        trie.verify_account_proof(root, answer)
    assert error.value.code == 502


def test_slot_not_rlp_word() -> None:
    """A slot whose value is not the RLP encoding of a word does not hold, with its index."""
    # Fixture: a valid account whose storage root is that of a trie with one leaf.
    # The value of that leaf is 0xc0, the empty list.
    # The balance and the nonce are 0, so the fields of the answer match.
    # Why: the account check passes, so the check of the slot is reached.
    account_node = (
        "f86aa120e2c07404b8c1df4c46226425cac68c28d27a766bbddce62309f36724839b22c0"
        "b846f8448080a0786f633dca032934929785b4c30dec1afc9f7fa80cb6f77aa90a08d7dc45385f"
        "a00000000000000000000000000000000000000000000000000000000000000000"
    )
    slot_node = "e4a120b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf681c0"
    root = bytes.fromhex("5fb81d7a5a3e969d850a4f99d6b5b127882833849f6e1d6d7af6fbbb7464b3cb")
    storage_root = "0x786f633dca032934929785b4c30dec1afc9f7fa80cb6f77aa90a08d7dc45385f"
    answer = {
        "address": _ADDRESS,
        "nonce": "0x0",
        "balance": "0x0",
        "codeHash": _ZERO,
        "storageHash": storage_root,
        "accountProof": ["0x" + account_node],
        "storageProof": [{"key": "0x1", "value": "0x0", "proof": ["0x" + slot_node]}],
    }
    with raises(
        TrieError, "answer does not hold: EthLib.Execution.State.AccountProofError.slotEncoding 0"
    ) as error:
        trie.verify_account_proof(root, answer)
    assert error.value.code == 505
