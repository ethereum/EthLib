"""Write the generalized indices, Merkle proofs and chunk roots of the SSZ package as vectors."""

import json
import sys
from hashlib import sha256
from pathlib import Path

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    SSZError,
    SSZType,
    Uint8,
    Uint16,
    Uint64,
    Uint256,
    Vector,
    build_proof,
    get_generalized_index,
    hash_tree_root,
    merkleize,
)

# The width in bytes of each unsigned integer type.
UINTS = {Uint8: 1, Uint16: 2, Uint64: 8, Uint256: 32}


def sized(base: type, name: str, **capacity: int) -> type:
    """A subclass of a shape that declares its length or its limit."""
    return type(name, (base,), capacity)


Bytes32 = sized(ByteVector, "Bytes32", LENGTH=32)
BitList8 = sized(BitList, "BitList8", LIMIT=8)
BitVector300 = sized(BitVector, "BitVector300", LENGTH=300)
ByteList64 = sized(ByteList, "ByteList64", LIMIT=64)
Uint16List4 = sized(List[Uint16], "Uint16List4", LIMIT=4)
Uint64List0 = sized(List[Uint64], "Uint64List0", LIMIT=0)
Uint64List8 = sized(List[Uint64], "Uint64List8", LIMIT=8)
Uint16Vector5 = sized(Vector[Uint16], "Uint16Vector5", LENGTH=5)
Uint64List2p40 = sized(List[Uint64], "Uint64List2p40", LIMIT=2**40)
# 2^64 chunks, so the indices of its elements and the depth of its proofs pass 2^64.
Uint256List2p64 = sized(List[Uint256], "Uint256List2p64", LIMIT=2**64)
RootList4 = sized(List[Bytes32], "RootList4", LIMIT=4)
RootList5 = sized(List[Bytes32], "RootList5", LIMIT=5)
RootVector3 = sized(Vector[Bytes32], "RootVector3", LENGTH=3)
Uint64Progressive = type("Uint64Progressive", (ProgressiveList[Uint64],), {})
Bits = type("Bits", (ProgressiveBitList,), {})


class Pair(Container):
    """A fixed field and a variable one."""

    a: Uint16
    b: Uint16List4


PairList5 = sized(List[Pair], "PairList5", LIMIT=5)


class Nested(Container):
    """Five fields, so eight leaves: a nested container, a list of them, roots and bits."""

    slot: Uint64
    pair: Pair
    pairs: PairList5
    roots: RootVector3
    flags: BitList8


class Square(ProgressiveContainer):
    """Fields at layout positions 0 and 2, with a gap at 1."""

    ACTIVE_FIELDS = (1, 0, 1)
    side: Uint16
    color: Uint8


class Circle(ProgressiveContainer):
    """Fields at layout positions 1 and 2, with a gap at 0."""

    ACTIVE_FIELDS = (0, 1, 1)
    radius: Uint16
    color: Uint8


class Shape(CompatibleUnion):
    """Two options that share the tree position of their color."""

    OPTIONS = {1: Square, 2: Circle}


TYPES: dict[str, type] = {
    "uint64": Uint64,
    "nested": Nested,
    "uint64_list_0": Uint64List0,
    "uint64_list_8": Uint64List8,
    "uint16_vector_5": Uint16Vector5,
    "uint64_list_2p40": Uint64List2p40,
    "uint256_list_2p64": Uint256List2p64,
    "root_list_4": RootList4,
    "root_list_5": RootList5,
    "byte_list_64": ByteList64,
    "bitlist_8": BitList8,
    "bitvector_300": BitVector300,
    "uint64_progressive": Uint64Progressive,
    "progressive_bitlist": Bits,
    "square": Square,
    "shape": Shape,
}


def tagged(cls: type) -> object:
    """The type in the tagged form of the EthLib bindings."""
    if cls in UINTS:
        return {"uint": UINTS[cls]}
    if cls is Boolean:
        return "bool"
    if issubclass(cls, ByteVector):
        return {"byte_vector": cls.LENGTH}
    if issubclass(cls, ByteList):
        return {"byte_list": cls.LIMIT}
    if issubclass(cls, BitVector):
        return {"bitvector": cls.LENGTH}
    if issubclass(cls, ProgressiveBitList):
        return {"progressive_bitlist": None}
    if issubclass(cls, BitList):
        return {"bitlist": cls.LIMIT}
    if issubclass(cls, ProgressiveList):
        return {"progressive_list": [tagged(cls.ELEMENT_TYPE), None]}
    if issubclass(cls, Vector):
        return {"vector": [tagged(cls.ELEMENT_TYPE), cls.LENGTH]}
    if issubclass(cls, List):
        return {"list": [tagged(cls.ELEMENT_TYPE), cls.LIMIT]}
    if issubclass(cls, CompatibleUnion):
        return {"compatible_union": [[s, tagged(t)] for s, t in cls.OPTIONS.items()]}
    if not issubclass(cls, (Container, ProgressiveContainer)):
        raise TypeError(cls)
    fields = [[name, tagged(field.annotation)] for name, field in cls.model_fields.items()]
    if issubclass(cls, ProgressiveContainer):
        return {"progressive_container": [[bool(b) for b in cls.ACTIVE_FIELDS], fields]}
    return {"container": fields}


# The paths of each type, through fields, positions and mixed-in words.
# Some leave the tree, some name what the type does not have, and some take a step it refuses.
PATHS: dict[str, list[list[int | str]]] = {
    "nested": [
        [],
        ["slot"],
        ["pair"],
        ["pair", "a"],
        ["pair", "b"],
        ["pair", "b", "__len__"],
        ["pair", "b", 0],
        ["pair", "b", 3],
        ["pair", "b", 4],
        ["pairs"],
        ["pairs", "__len__"],
        ["pairs", 0],
        ["pairs", 4],
        ["pairs", 5],
        ["pairs", 1, "a"],
        ["pairs", 1, "b", 2],
        ["pairs", 1, "b", "__len__"],
        ["pairs", 9, "a"],
        ["roots", 0],
        ["roots", 2],
        ["roots", 3],
        ["flags", "__len__"],
        ["flags", 0],
        ["flags", 7],
        ["flags", 8],
        ["missing"],
        [1],
        ["pair", 0],
        ["slot", 0],
        ["slot", "__len__"],
        ["pairs", "__len__", 0],
        ["__len__"],
        ["__selector__"],
        ["__active_fields__"],
    ],
    "uint64_list_0": [["__len__"], [0]],
    "uint64_list_8": [["__len__"], [0], [3], [4], [7], [8]],
    "uint16_vector_5": [[0], [4], [5], ["__len__"]],
    "uint64_list_2p40": [["__len__"], [5], [2**40 - 1], [2**40]],
    "uint256_list_2p64": [["__len__"], [0], [2**64 - 1], [2**64]],
    "root_list_4": [["__len__"], [0], [3], [4]],
    "root_list_5": [["__len__"], [0], [4], [5]],
    "byte_list_64": [["__len__"], [0], [31], [32], [63], [64]],
    "bitlist_8": [["__len__"], [0], [7], [8]],
    "bitvector_300": [[0], [255], [256], [299], [300], ["__len__"]],
    "uint64_progressive": [["__len__"], [0], [3], [4], [5], [100]],
    "progressive_bitlist": [["__len__"], [0], [255], [256], [1000]],
    "square": [
        ["side"],
        ["color"],
        ["__active_fields__"],
        ["radius"],
        [0],
        ["side", 0],
        ["__active_fields__", 0],
        ["__selector__"],
        ["__len__"],
    ],
    "shape": [
        [1, "side"],
        [1, "color"],
        [2, "radius"],
        [2, "color"],
        [1],
        ["__selector__"],
        [3],
        [3, "color"],
        [1, 0],
        [1, "radius"],
        ["__selector__", 1],
        ["__active_fields__"],
        ["color"],
        [1, "__active_fields__"],
    ],
}


def roots(count: int) -> list[bytes]:
    """Distinct 32-byte roots, the digests of the numbers 0 to count - 1."""
    return [sha256(bytes([i])).digest() for i in range(count)]


def pair(a: int, b: list[int]) -> Pair:
    """A pair of a number and a list of at most four numbers."""
    return Pair(a=Uint16(a), b=Uint16List4(data=[Uint16(x) for x in b]))


# The values to prove into, by name: empty lists, lists filled to a power-of-two limit, and more.
VALUES: dict[str, tuple[str, SSZType]] = {
    "uint64": ("uint64", Uint64(7)),
    "nested_empty": (
        "nested",
        Nested(
            slot=Uint64(0),
            pair=pair(0, []),
            pairs=PairList5(data=[]),
            roots=RootVector3(data=[Bytes32(bytes(32))] * 3),
            flags=BitList8(data=[]),
        ),
    ),
    "nested": (
        "nested",
        Nested(
            slot=Uint64(7),
            pair=pair(1, [2, 3]),
            pairs=PairList5(data=[pair(4, []), pair(5, [6, 7, 8, 9])]),
            roots=RootVector3(data=[Bytes32(r) for r in roots(3)]),
            flags=BitList8(data=[Boolean(b) for b in (True, False, True)]),
        ),
    ),
    "uint64_list_0": ("uint64_list_0", Uint64List0(data=[])),
    "uint16_vector_5": ("uint16_vector_5", Uint16Vector5(data=[Uint16(n) for n in range(1, 6)])),
    "uint64_list_8_empty": ("uint64_list_8", Uint64List8(data=[])),
    "uint64_list_8_three": ("uint64_list_8", Uint64List8(data=[Uint64(n) for n in (1, 2, 3)])),
    "uint64_list_8_full": ("uint64_list_8", Uint64List8(data=[Uint64(n) for n in range(8)])),
    "uint64_list_2p40": ("uint64_list_2p40", Uint64List2p40(data=[Uint64(n) for n in range(9)])),
    "uint256_list_2p64": ("uint256_list_2p64", Uint256List2p64(data=[Uint256(2**256 - 1)])),
    "root_list_4_empty": ("root_list_4", RootList4(data=[])),
    "root_list_4_full": ("root_list_4", RootList4(data=[Bytes32(r) for r in roots(4)])),
    "root_list_5_full": ("root_list_5", RootList5(data=[Bytes32(r) for r in roots(5)])),
    "byte_list_64": ("byte_list_64", ByteList64(data=bytes(range(1, 34)))),
    "bitlist_8_full": ("bitlist_8", BitList8(data=[Boolean(True)] * 8)),
    "bitvector_300": (
        "bitvector_300",
        BitVector300(data=[Boolean(i % 3 == 0) for i in range(300)]),
    ),
    "uint64_progressive_empty": ("uint64_progressive", Uint64Progressive(data=[])),
    "uint64_progressive_three": (
        "uint64_progressive",
        Uint64Progressive(data=[Uint64(n) for n in range(3)]),
    ),
    "uint64_progressive_thirty": (
        "uint64_progressive",
        Uint64Progressive(data=[Uint64(n) for n in range(30)]),
    ),
    "progressive_bitlist": (
        "progressive_bitlist",
        Bits(data=[Boolean(i % 5 == 0) for i in range(300)]),
    ),
    "square": ("square", Square(side=Uint16(3), color=Uint8(9))),
    "shape_circle": (
        "shape",
        Shape(selector=Uint8(2), data=Circle(radius=Uint16(5), color=Uint8(1))),
    ),
}

# Every index below this bound is proved in every value, besides the indices of its paths.
INDEX_BOUND = 32

# An index far below the tree of every value, which a 64-bit or 128-bit integer cannot hold.
DEEP_INDEX = 2**200

# Chunk lists and limits, among them empty lists and limits at, below and above a power of two.
# Equal chunks and zero chunks take the shortcuts of the package, which must give the same root.
CHUNKS: list[tuple[list[bytes], int | None]] = [
    ([], None),
    ([], 0),
    ([], 1),
    ([], 2),
    ([], 4),
    ([], 2**10),
    (roots(1), None),
    (roots(1), 1),
    (roots(1), 2),
    (roots(3), None),
    (roots(3), 3),
    (roots(3), 4),
    (roots(3), 5),
    (roots(3), 8),
    (roots(4), None),
    (roots(4), 4),
    (roots(5), 8),
    (roots(5), 2**20),
    (roots(1), 2**64),
    ([bytes(32)] * 4, None),
    ([bytes(32)] * 3, 8),
    ([roots(1)[0]] * 4, 4),
    ([roots(1)[0]] * 6, 16),
    (roots(3), 2),
    (roots(1), 0),
    (roots(4), 3),
]


def fault(error: SSZError) -> dict[str, object]:
    """The fault the package names, and the step, index, count or limit it reports."""
    kept = {k: v for k, v in error.fields.items() if k in ("step", "index", "count", "limit")}
    return {"fault": error.fault.name, **kept}


def gindex_case(name: str, path: list[int | str]) -> dict[str, object]:
    """The generalized index of a path, or the fault that refuses it."""
    case: dict[str, object] = {"type": name, "path": path}
    try:
        case["gindex"] = get_generalized_index(TYPES[name], *path)
    except SSZError as error:
        case["gindex"] = None
        case.update(fault(error))
    return case


def proof_case(value: SSZType, gindex: int) -> dict[str, object]:
    """The branch of a generalized index in a value, bottom first, or the fault that refuses it."""
    case: dict[str, object] = {"gindex": gindex}
    try:
        case["branch"] = ["0x" + bytes(node).hex() for node in build_proof(value, gindex)]
    except SSZError as error:
        case["branch"] = None
        case.update(fault(error))
    return case


def chunk_case(chunks: list[bytes], limit: int | None) -> dict[str, object]:
    """The root of chunks under a limit, or the fault that refuses them."""
    case: dict[str, object] = {"chunks": ["0x" + c.hex() for c in chunks], "limit": limit}
    try:
        case["root"] = "0x" + bytes(merkleize(chunks, limit)).hex()
    except SSZError as error:
        # The case keeps its own limit, which the fault repeats.
        assert error.fields["limit"] == limit
        case["root"] = None
        case.update(fault(error))
    return case


def main(out: Path) -> None:
    """Write the cases as one JSON file."""
    gindices = [gindex_case(name, path) for name, paths in PATHS.items() for path in paths]
    values = []
    for value_name, (type_name, value) in VALUES.items():
        data = value.encode_bytes()
        assert TYPES[type_name].decode_bytes(data) == value
        reached = {
            c["gindex"] for c in gindices if c["type"] == type_name and c["gindex"] is not None
        }
        indices = sorted(set(range(INDEX_BOUND)) | reached | {DEEP_INDEX})
        values.append(
            {
                "name": value_name,
                "type": type_name,
                "serialized": "0x" + data.hex(),
                "root": "0x" + bytes(hash_tree_root(value)).hex(),
                "proofs": [proof_case(value, gindex) for gindex in indices],
            }
        )
    cases = {
        "types": {name: tagged(cls) for name, cls in TYPES.items()},
        "generalized_indices": gindices,
        "values": values,
        "chunk_roots": [chunk_case(chunks, limit) for chunks, limit in CHUNKS],
    }
    (out / "cases.json").write_text(json.dumps(cases, indent=1) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
