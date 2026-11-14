"""Generalized indices, Merkle proofs and chunk roots, checked against hashlib and the SSZ rules."""

import hashlib

import pytest

from ethlib.errors import SszError
from ethlib.serialization import ssz
from raising import raises

UINT8 = {"uint": 1}
UINT16 = {"uint": 2}
UINT64 = {"uint": 8}
BYTES32 = {"byte_vector": 32}

# A container of a fixed field a: uint16 and a variable field b: List[uint16, 4].
MIXED_PAIR = {"container": [["a", UINT16], ["b", {"list": [UINT16, 4]}]]}

# A container with a nested container, a list of containers and a vector of roots.
NESTED = {
    "container": [
        ["slot", UINT64],
        ["pair", MIXED_PAIR],
        ["pairs", {"list": [MIXED_PAIR, 5]}],
        ["roots", {"vector": [BYTES32, 3]}],
    ]
}

# Progressive containers whose layout bits place their fields, and a union of them.
SQUARE = {"progressive_container": [[True, False, True], [["side", UINT16], ["color", UINT8]]]}
CIRCLE = {"progressive_container": [[False, True, True], [["radius", UINT16], ["color", UINT8]]]}
UNION = {"compatible_union": [[1, SQUARE], [2, CIRCLE], [127, SQUARE]]}


def _uints(values: list[int]) -> dict:
    return {"seq": [{"uint": n} for n in values]}


def _pair(a: int, b: list[int]) -> dict:
    return {"seq": [{"uint": a}, _uints(b)]}


PAIR = _pair(1, [2, 3])
SECOND_PAIR = _pair(5, [6, 7, 8, 9])
ROOT = bytes([2]) * 32
ROOTS = {"seq": [{"bytes": "0x" + (bytes([i]) * 32).hex()} for i in range(3)]}
NESTED_VALUE = {"seq": [{"uint": 7}, PAIR, {"seq": [_pair(4, []), SECOND_PAIR]}, ROOTS]}
SQUARE_VALUE = {"seq": [{"uint": 3}, {"uint": 9}]}

# A progressive list of uint64, and a value of three elements that all fit its first chunk.
PROGRESSIVE = {"progressive_list": [UINT64, None]}
PROGRESSIVE_VALUE = _uints([0, 1, 2])


def _sha(left: bytes, right: bytes) -> bytes:
    return hashlib.sha256(left + right).digest()


def _climb(node: bytes, gindex: int, branch: list[bytes]) -> bytes:
    """The root that a node and its branch reach, by the bits of its generalized index."""
    for sibling in branch:
        node = _sha(sibling, node) if gindex & 1 else _sha(node, sibling)
        gindex >>= 1
    assert gindex == 1
    return node


# Each path, its index, the type it reaches and the value there, with the index from the SSZ rules.
# Four fields pad to four leaves, at 4 to 7, and the two fields of a pair sit below it.
# A list hangs its contents at its left child and its length at its right child.
# Five pairs pad to eight leaves, so pair 1 sits at 12 * 8 + 1 = 97, below the contents node 12.
# Three roots pad to four leaves, so root 2 sits at 7 * 4 + 2.
PATHS = [
    ([], 1, NESTED, NESTED_VALUE),
    (["slot"], 4, UINT64, {"uint": 7}),
    (["pair"], 5, MIXED_PAIR, PAIR),
    ([1], 5, MIXED_PAIR, PAIR),
    (["pair", "a"], 10, UINT16, {"uint": 1}),
    (["pair", "b"], 11, {"list": [UINT16, 4]}, _uints([2, 3])),
    (["pair", "b", "__len__"], 23, UINT64, {"uint": 2}),
    (["pairs", "__len__"], 13, UINT64, {"uint": 2}),
    (["pairs", 1], 97, MIXED_PAIR, SECOND_PAIR),
    (["pairs", 1, "b"], 97 * 2 + 1, {"list": [UINT16, 4]}, _uints([6, 7, 8, 9])),
    (["roots", 2], 7 * 4 + 2, BYTES32, {"bytes": "0x" + ROOT.hex()}),
]


@pytest.mark.parametrize(("path", "gindex", "_type", "_value"), PATHS)
def test_generalized_index(path, gindex, _type, _value):
    assert ssz.get_generalized_index(NESTED, *path) == gindex


# 2**40 uint64 fill 2**38 chunks, and element 5 is in chunk 1, below the contents node 2.
# Four uint16 fill one chunk, so every element of List[uint16, 4] is the contents node 22 itself.
# A bit list of limit 8 has one chunk, which is its contents node 2.
# The square's fields sit at chunks 0 and 2 of the spine below the contents node 2.
# Chunk 0 is the first leaf of the spine, at 4.
# Chunk 2 is the second leaf of the second spine level: 6 * 4 + 1 = 25 below 2, so 2 * 16 + 9.
# A union puts the chosen option at 2, so the square's color is 2 * 32 + 9.
# Four uint64 fill a chunk of a progressive list, and each spine level holds four times more.
# Element 5 is in chunk 1, the first leaf of level 2: 6 * 4 = 24 below 2, so 2 * 16 + 8.
# Element 100 is in chunk 25, leaf 4 of level 4: 30 * 64 + 4 = 1924 below 2, so 2 * 1024 + 900.
OTHER_PATHS = [
    ({"list": [UINT64, 2**40]}, [5], 2 * 2**38 + 1),
    (NESTED, ["pairs", 4], 12 * 8 + 4),
    (NESTED, ["pair", "b", 3], 22),
    ({"bitlist": 8}, [3], 2),
    (PROGRESSIVE, ["__len__"], 3),
    (PROGRESSIVE, [0], 4),
    (PROGRESSIVE, [5], 40),
    (PROGRESSIVE, [100], 2948),
    (SQUARE, ["side"], 4),
    (SQUARE, ["color"], 41),
    (UNION, [1, "color"], 73),
]


@pytest.mark.parametrize(("ssz_type", "path", "gindex"), OTHER_PATHS)
def test_generalized_index_of_other_shapes(ssz_type, path, gindex):
    assert ssz.get_generalized_index(ssz_type, *path) == gindex


# A path that leaves the tree, and the fault of the step that leaves it.
OUT_OF_TREE = [
    (NESTED, ["pairs", 5], "noSuchPosition 5"),
    (NESTED, ["roots", 3], "noSuchPosition 3"),
    (NESTED, ["pair", "b", 4], "noSuchPosition 4"),
    ({"bitlist": 8}, [8], "noSuchPosition 8"),
    (UNION, [3], "noSuchOption 3"),
    (MIXED_PAIR, ["a", 0], "noParts"),
    (MIXED_PAIR, ["b", "__len__", 0], "noPartsMixin"),
    # A field name after a refused step gets the fault of that step.
    (NESTED, ["pairs", 9, "a"], "noSuchPosition 9"),
    (UNION, [3, "color"], "noSuchOption 3"),
    (MIXED_PAIR, ["b", "__len__", "x"], "noPartsMixin"),
]


@pytest.mark.parametrize(("ssz_type", "path", "fault"), OUT_OF_TREE)
def test_generalized_index_refuses_a_path_out_of_the_tree(ssz_type, path, fault):
    with raises(SszError, "path rejected: EthLib.Serialization.Ssz.Err." + fault):
        ssz.get_generalized_index(ssz_type, *path)


def test_generalized_index_refuses_an_unknown_field():
    with raises(SszError, "path: no field c"):
        ssz.get_generalized_index(MIXED_PAIR, "c")


# The root has no branch.
PROVEN = [path for path in PATHS if path[1] != 1]


@pytest.mark.parametrize(("path", "gindex", "sub_type", "sub_value"), PROVEN)
def test_merkle_proof_reaches_the_root(path, gindex, sub_type, sub_value):
    # The node at the index is the root of the value the path reaches.
    node = ssz.hash_tree_root(sub_type, sub_value)
    branch = ssz.compute_merkle_proof(NESTED, NESTED_VALUE, gindex)
    assert len(branch) == gindex.bit_length() - 1
    assert _climb(node, gindex, branch) == ssz.hash_tree_root(NESTED, NESTED_VALUE)


def test_merkle_proof_of_an_absent_element():
    # Pair 3 of a list that holds two is padding, so its node is the zero chunk.
    gindex = ssz.get_generalized_index(NESTED, "pairs", 3)
    branch = ssz.compute_merkle_proof(NESTED, NESTED_VALUE, gindex)
    assert _climb(bytes(32), gindex, branch) == ssz.hash_tree_root(NESTED, NESTED_VALUE)


@pytest.mark.parametrize(
    ("ssz_type", "value", "path", "leaf_type", "leaf"),
    [
        (SQUARE, SQUARE_VALUE, ["side"], UINT16, 3),
        (SQUARE, SQUARE_VALUE, ["color"], UINT8, 9),
        (UNION, {"union": [1, SQUARE_VALUE]}, [1, "color"], UINT8, 9),
    ],
)
def test_merkle_proof_in_progressive_shapes(ssz_type, value, path, leaf_type, leaf):
    gindex = ssz.get_generalized_index(ssz_type, *path)
    node = ssz.hash_tree_root(leaf_type, {"uint": leaf})
    branch = ssz.compute_merkle_proof(ssz_type, value, gindex)
    assert _climb(node, gindex, branch) == ssz.hash_tree_root(ssz_type, value)


def test_merkle_proof_in_a_progressive_list():
    # The three elements share the first chunk, little-endian and padded with zeros.
    node = b"".join(n.to_bytes(8, "little") for n in range(3)).ljust(32, b"\0")
    branch = ssz.compute_merkle_proof(PROGRESSIVE, PROGRESSIVE_VALUE, 4)
    assert len(branch) == 2
    assert _climb(node, 4, branch) == ssz.hash_tree_root(PROGRESSIVE, PROGRESSIVE_VALUE)


def test_merkle_proof_of_every_node_of_a_vector():
    vector = {"vector": [BYTES32, 4]}
    chunks = [bytes([i]) * 32 for i in range(4)]
    value = {"seq": [{"bytes": "0x" + chunk.hex()} for chunk in chunks]}
    left, right = _sha(chunks[0], chunks[1]), _sha(chunks[2], chunks[3])
    nodes = {2: left, 3: right, 4: chunks[0], 5: chunks[1], 6: chunks[2], 7: chunks[3]}
    root = _sha(left, right)
    for gindex, node in nodes.items():
        branch = ssz.compute_merkle_proof(vector, value, gindex)
        assert _climb(node, gindex, branch) == root
    assert ssz.compute_merkle_proof(vector, value, 5) == [chunks[0], right]


# An index that the tree of the value does not hold, and the fault of the proof.
OUTSIDE = [
    # Below the uint64 leaf of the slot.
    (NESTED, NESTED_VALUE, 8, "pathIntoPacked"),
    # Below pair 3, at 99, of a list that holds two pairs.
    (NESTED, NESTED_VALUE, 99 * 2, "pathIntoGap"),
    # Below the length word of a list.
    ({"list": [MIXED_PAIR, 5]}, {"seq": []}, 3 * 2 + 1, "pathIntoMixin"),
    # Below the second spine level of a progressive list that fills only its first chunk.
    (PROGRESSIVE, PROGRESSIVE_VALUE, 40, "pathPastSpine"),
    (MIXED_PAIR, PAIR, 0, "notAGindex 0"),
    (MIXED_PAIR, PAIR, 1, "rootHasNoBranch"),
]


@pytest.mark.parametrize(("ssz_type", "value", "gindex", "fault"), OUTSIDE)
def test_merkle_proof_refuses_an_index_outside_the_tree(ssz_type, value, gindex, fault):
    with raises(SszError, "proof rejected: EthLib.Serialization.Ssz.Err." + fault):
        ssz.compute_merkle_proof(ssz_type, value, gindex)


def test_merkle_proof_refuses_a_value_that_does_not_fit():
    too_long = _pair(1, [1, 2, 3, 4, 5])
    with raises(SszError, "value rejected: EthLib.Serialization.Ssz.Err.overLimit 4 5"):
        ssz.compute_merkle_proof(MIXED_PAIR, too_long, 2)


def test_merkleize_chunks():
    chunks = [bytes([i]) * 32 for i in range(3)]
    zero = bytes(32)
    three = _sha(_sha(chunks[0], chunks[1]), _sha(chunks[2], zero))
    assert ssz.merkleize_chunks(chunks) == three
    assert ssz.merkleize_chunks(tuple(chunks), 4) == three
    assert ssz.merkleize_chunks(chunks, 8) == _sha(three, _sha(_sha(zero, zero), _sha(zero, zero)))
    assert ssz.merkleize_chunks([chunks[0]]) == chunks[0]
    assert ssz.merkleize_chunks([chunks[0]], 1) == chunks[0]
    assert ssz.merkleize_chunks([]) == zero
    assert ssz.merkleize_chunks([], 0) == zero
    assert ssz.merkleize_chunks([], 2) == _sha(zero, zero)


def test_merkleize_chunks_is_the_root_of_a_vector_of_roots():
    chunks = [hashlib.sha256(bytes([i])).digest() for i in range(5)]
    value = {"seq": [{"bytes": "0x" + chunk.hex()} for chunk in chunks]}
    root = ssz.hash_tree_root({"vector": [BYTES32, 5]}, value)
    assert ssz.merkleize_chunks(chunks) == root
    assert ssz.merkleize_chunks(chunks, 5) == root


@pytest.mark.parametrize(
    ("chunks", "limit", "fault"),
    [
        ([bytes(32)] * 3, 2, "merkleizeLimit 3 2"),
        ([bytes(32)], 0, "merkleizeLimit 1 0"),
        ([bytes(32), bytes(31)], None, "count 32 31"),
        ([bytes(33)], None, "count 32 33"),
    ],
)
def test_merkleize_chunks_refuses(chunks, limit, fault):
    with raises(SszError, "chunks rejected: EthLib.Serialization.Ssz.Err." + fault):
        ssz.merkleize_chunks(chunks, limit)
