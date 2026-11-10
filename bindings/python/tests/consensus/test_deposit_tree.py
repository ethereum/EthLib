"""The deposit tree and its EIP-4881 snapshot against the test cases of the EIP."""

import hashlib
from collections.abc import Iterable
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import Any

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.consensus import DepositSubtree, DepositTree, DepositTreeSnapshot, Eth1Data
from ethlib.errors import DepositTreeError
from ethlib.serialization import ssz
from raising import raises

CASES = Path(__file__).parent / "deposit_tree" / "test_cases.yaml"

DEPTH = 32


def _empty_root() -> bytes:
    """The root of the empty tree: the zero subtree of height 32, then the count zero mixed in."""
    node = bytes(32)
    for _ in range(DEPTH):
        node = hashlib.sha256(node + node).digest()
    return hashlib.sha256(node + bytes(32)).digest()


EMPTY_ROOT = _empty_root()

# The messages that reject a tree that no operation builds.
SHAPE = "the subtrees do not have the shape of a deposit tree"
NO_BLOCK = "a tree with finalized deposits has a finalized block"

# The SSZ type of deposit data: a public key, withdrawal credentials, an amount and a signature.
DEPOSIT_DATA = {
    "container": [
        ["pubkey", {"byte_vector": 48}],
        ["withdrawal_credentials", {"byte_vector": 32}],
        ["amount", {"uint": 8}],
        ["signature", {"byte_vector": 96}],
    ]
}


@dataclass(frozen=True, slots=True)
class Case:
    """One deposit of the EIP: its data and leaf, the deposit data after it, and the snapshot."""

    deposit_data: dict[str, Any]
    leaf: bytes
    eth1_data: Eth1Data
    block_height: int
    snapshot: DepositTreeSnapshot


def _hex(text: str) -> bytes:
    """The bytes of a hex string with its 0x prefix."""
    return bytes.fromhex(text.removeprefix("0x"))


@cache
def cases() -> tuple[Case, ...]:
    """The test cases of the EIP, in order."""
    loaded = YAML(typ="safe").load(CASES.read_text())
    result = []
    for case in loaded:
        data = case["deposit_data"]
        eth1 = case["eth1_data"]
        snapshot = case["snapshot"]
        result.append(
            Case(
                deposit_data={
                    "seq": [
                        {"bytes": data["pubkey"]},
                        {"bytes": data["withdrawal_credentials"]},
                        {"uint": int(data["amount"])},
                        {"bytes": data["signature"]},
                    ]
                },
                leaf=_hex(case["deposit_data_root"]),
                eth1_data=(
                    _hex(eth1["deposit_root"]),
                    int(eth1["deposit_count"]),
                    _hex(eth1["block_hash"]),
                ),
                block_height=int(case["block_height"]),
                snapshot=(
                    [_hex(root) for root in snapshot["finalized"]],
                    _hex(snapshot["deposit_root"]),
                    int(snapshot["deposit_count"]),
                    _hex(snapshot["execution_block_hash"]),
                    int(snapshot["execution_block_height"]),
                ),
            )
        )
    return tuple(result)


def pushed(tree: DepositTree, leaves: Iterable[Case]) -> DepositTree:
    """The tree after pushing the leaves of the cases in order."""
    return consensus.deposit_tree_push_leaves(tree, [case.leaf for case in leaves])


def finalized(tree: DepositTree, case: Case) -> DepositTree:
    """The tree finalized at the deposit data and the block height of a case."""
    return consensus.deposit_tree_finalize(tree, case.eth1_data, case.block_height)


def climb(leaf: bytes, proof: list[bytes], index: int) -> bytes:
    """The root that a leaf and its proof reach: the branch from the leaf up, then the count."""
    node = leaf
    for level, sibling in enumerate(proof[:DEPTH]):
        if (index >> level) & 1:
            node = hashlib.sha256(sibling + node).digest()
        else:
            node = hashlib.sha256(node + sibling).digest()
    return hashlib.sha256(node + proof[DEPTH]).digest()


def assert_proofs(tree: DepositTree, indices: range, root: bytes) -> None:
    """Every index has its pushed leaf, and a proof that climbs to the given deposit root."""
    for index in indices:
        leaf, proof = consensus.deposit_tree_get_proof(tree, index)
        assert leaf == cases()[index].leaf
        assert len(proof) == DEPTH + 1
        assert climb(leaf, proof, index) == root


def almost_full(height: int, root: bytes) -> list[DepositSubtree]:
    """The preorder of a subtree with every leaf but the last finalized, all with one root."""
    if height == 1:
        return ["node", ("finalized", 1, root), ("zero", 0)]
    return ["node", ("finalized", 2 ** (height - 1), root), *almost_full(height - 1, root)]


def test_case_count() -> None:
    assert len(cases()) == 512


def test_leaves_are_deposit_data_roots() -> None:
    for case in cases():
        assert ssz.hash_tree_root(DEPOSIT_DATA, case.deposit_data) == case.leaf


def test_empty_root() -> None:
    assert consensus.deposit_tree_get_root(consensus.deposit_tree_new()) == EMPTY_ROOT


def test_deposit_roots() -> None:
    tree = consensus.deposit_tree_new()
    for case in cases():
        tree = consensus.deposit_tree_push_leaf(tree, case.leaf)
        assert consensus.deposit_tree_get_root(tree) == case.eth1_data[0]
        assert consensus.deposit_tree_snapshot_calculate_root(case.snapshot) == case.eth1_data[0]


def test_push_leaves_is_push_leaf_in_order() -> None:
    one_by_one = consensus.deposit_tree_new()
    for case in cases()[:40]:
        one_by_one = consensus.deposit_tree_push_leaf(one_by_one, case.leaf)
    assert pushed(consensus.deposit_tree_new(), cases()[:40]) == one_by_one


def test_snapshots() -> None:
    tree = pushed(consensus.deposit_tree_new(), cases())
    root = consensus.deposit_tree_get_root(tree)
    for case in cases():
        tree = finalized(tree, case)
        assert consensus.deposit_tree_get_snapshot(tree) == case.snapshot
        assert consensus.deposit_tree_get_root(tree) == root
        rebuilt = consensus.deposit_tree_from_snapshot(case.snapshot)
        assert consensus.deposit_tree_get_snapshot(rebuilt) == case.snapshot


def test_finalization() -> None:
    first = cases()[:128]
    tree = pushed(consensus.deposit_tree_new(), first)
    root = consensus.deposit_tree_get_root(tree)
    assert root == first[127].eth1_data[0]
    tree = finalized(tree, first[100])
    assert consensus.deposit_tree_get_root(tree) == root
    snapshot = consensus.deposit_tree_get_snapshot(tree)
    assert snapshot == first[100].snapshot
    copy = pushed(consensus.deposit_tree_from_snapshot(snapshot), first[101:])
    assert consensus.deposit_tree_get_root(copy) == root
    # A second finalization leaves the root as it was.
    tree = finalized(tree, first[105])
    assert consensus.deposit_tree_get_root(tree) == root
    copy = pushed(
        consensus.deposit_tree_from_snapshot(consensus.deposit_tree_get_snapshot(tree)), first[106:]
    )
    full = pushed(consensus.deposit_tree_new(), first)
    for index in range(106, 128):
        proof = consensus.deposit_tree_get_proof(tree, index)
        assert consensus.deposit_tree_get_proof(copy, index) == proof
        assert consensus.deposit_tree_get_proof(full, index) == proof
    assert_proofs(tree, range(106, 128), first[127].eth1_data[0])


def test_rebuilt_tree_follows_later_deposits() -> None:
    tree = consensus.deposit_tree_from_snapshot(cases()[100].snapshot)
    for case in cases()[101:]:
        tree = consensus.deposit_tree_push_leaf(tree, case.leaf)
        assert consensus.deposit_tree_get_root(tree) == case.eth1_data[0]


def test_proofs_of_every_leaf() -> None:
    assert_proofs(
        pushed(consensus.deposit_tree_new(), cases()), range(512), cases()[511].eth1_data[0]
    )


def test_snapshot_of_unfinalized_tree() -> None:
    with raises(DepositTreeError, "EthLib.Consensus.DepositTreeError.notFinalized"):
        consensus.deposit_tree_get_snapshot(consensus.deposit_tree_new())


def test_snapshot_with_wrong_root() -> None:
    # The empty tree has the root of an empty snapshot, not the zero root.
    with raises(DepositTreeError, "EthLib.Consensus.DepositTreeError.rootMismatch"):
        consensus.deposit_tree_from_snapshot(([], bytes(32), 0, bytes(32), 0))


def test_snapshot_with_extra_root() -> None:
    # A leading root that no bit of the count uses would place every subtree one slot right.
    roots, root, count, block_hash, height = cases()[100].snapshot
    extra = ([bytes(32), *roots], root, count, block_hash, height)
    with raises(DepositTreeError, "EthLib.Consensus.DepositTreeError.extraFinalized"):
        consensus.deposit_tree_from_snapshot(extra)


def test_snapshot_with_missing_root() -> None:
    roots, root, count, block_hash, height = cases()[100].snapshot
    missing = (roots[1:], root, count, block_hash, height)
    with raises(DepositTreeError, "EthLib.Consensus.DepositTreeError.missingFinalized"):
        consensus.deposit_tree_from_snapshot(missing)


def test_snapshot_beyond_capacity() -> None:
    with raises(
        DepositTreeError, "EthLib.Consensus.DepositTreeError.countBeyondCapacity 4294967296"
    ):
        consensus.deposit_tree_snapshot_calculate_root(([], bytes(32), 2**DEPTH, bytes(32), 0))


def test_snapshot_with_too_many_roots() -> None:
    with raises(DepositTreeError, "a snapshot holds at most 32 finalized roots"):
        consensus.deposit_tree_from_snapshot(([bytes(32)] * 33, bytes(32), 0, bytes(32), 0))


def test_finalize_beyond_count() -> None:
    tree = pushed(consensus.deposit_tree_new(), cases()[:3])
    with raises(DepositTreeError, "EthLib.Consensus.DepositTreeError.finalizeBeyondCount 4 3"):
        finalized(tree, cases()[3])


def test_finalize_below_an_earlier_finalization() -> None:
    tree = finalized(pushed(consensus.deposit_tree_new(), cases()[:128]), cases()[100])
    with raises(
        DepositTreeError, "EthLib.Consensus.DepositTreeError.finalizeBelowFinalized 51 101"
    ):
        finalized(tree, cases()[50])


def test_finalize_again_at_the_same_count() -> None:
    tree = finalized(pushed(consensus.deposit_tree_new(), cases()[:128]), cases()[100])
    again = consensus.deposit_tree_finalize(tree, cases()[100].eth1_data, 1000)
    assert consensus.deposit_tree_get_snapshot(again) == (*cases()[100].snapshot[:4], 1000)


def test_finalize_with_a_wrong_root() -> None:
    tree = pushed(consensus.deposit_tree_new(), cases()[:3])
    _, count, block_hash = cases()[1].eth1_data
    with raises(DepositTreeError, "EthLib.Consensus.DepositTreeError.rootMismatch"):
        consensus.deposit_tree_finalize(tree, (cases()[2].eth1_data[0], count, block_hash), 7)


def test_finalize_nothing() -> None:
    tree = pushed(consensus.deposit_tree_new(), cases()[:3])
    empty = consensus.deposit_tree_finalize(tree, (EMPTY_ROOT, 0, bytes(32)), 7)
    assert consensus.deposit_tree_get_snapshot(empty) == ([], EMPTY_ROOT, 0, bytes(32), 7)
    assert_proofs(empty, range(3), cases()[2].eth1_data[0])


def test_full_tree() -> None:
    # The deposit contract stops one deposit short of the leaves of its tree.
    root = bytes(32)
    tree: DepositTree = (almost_full(DEPTH, root), 2**DEPTH - 1, (root, 0))
    with raises(DepositTreeError, "EthLib.Consensus.DepositTreeError.treeFull"):
        consensus.deposit_tree_push_leaf(tree, root)


@pytest.mark.parametrize(
    ("index", "message"),
    [
        (99, "EthLib.Consensus.DepositTreeError.proofOfFinalized 99 101"),
        (100, "EthLib.Consensus.DepositTreeError.proofOfFinalized 100 101"),
        (128, "EthLib.Consensus.DepositTreeError.proofBeyondCount 128 128"),
    ],
)
def test_proof_outside_the_pending_deposits(index: int, message: str) -> None:
    tree = finalized(pushed(consensus.deposit_tree_new(), cases()[:128]), cases()[100])
    with raises(DepositTreeError, message):
        consensus.deposit_tree_get_proof(tree, index)


@pytest.mark.parametrize(
    ("tree", "message"),
    [
        ((["nod"], 0, None), "expected a tagged subtree"),
        (([("zero", b"x")], 0, None), "expected a tagged subtree"),
        ((["node", ("zero", 31)], 0, None), "a node needs two subtrees"),
        (([], 0, None), "expected exactly one tree"),
        (([("zero", 32), ("zero", 32)], 0, None), "expected exactly one tree"),
        (([("zero", 31)], 0, None), SHAPE),
        (([("leaf", bytes(32))], 1, None), SHAPE),
        (([("finalized", 3, bytes(32))], 3, None), SHAPE),
        (([("zero", 32)], 1, None), "the tree holds 0 deposits, not 1"),
        ((["node", ("zero", 31), ("zero", 31)], 0, None), SHAPE),
        ((almost_full(DEPTH, bytes(32)), 2**DEPTH - 1, None), NO_BLOCK),
        (
            ([("finalized", 2**DEPTH, bytes(32))], 2**DEPTH, (bytes(32), 0)),
            "a tree holds fewer than 2^32 deposits",
        ),
    ],
)
def test_malformed_tree(tree: DepositTree, message: str) -> None:
    with raises(DepositTreeError, message):
        consensus.deposit_tree_get_root(tree)


def test_leaf_beside_a_finalized_deposit() -> None:
    # A pending deposit left of a finalized one is no deposit tree.
    bottom: list[DepositSubtree] = ["node", ("leaf", bytes(32)), ("finalized", 1, bytes(32))]
    subtrees: list[DepositSubtree] = []
    for height in range(1, DEPTH):
        subtrees += ["node"]
        bottom += [("zero", height)]
    with raises(DepositTreeError, SHAPE):
        consensus.deposit_tree_get_root((subtrees + bottom, 2, (bytes(32), 0)))


def test_gapped_tree() -> None:
    # A right half with a deposit beside a left half with an empty leaf is no deposit tree.
    subtrees: list[DepositSubtree] = ["node", ("zero", 31), *almost_full(31, bytes(32))]
    with raises(DepositTreeError, SHAPE):
        consensus.deposit_tree_get_root((subtrees, 2**31 - 1, (bytes(32), 0)))
