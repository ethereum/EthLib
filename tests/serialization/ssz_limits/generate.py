"""Write the SSZ vectors of lists whose limits reach 2^32 or 2^64 bytes or chunks."""

import json
import sys
from pathlib import Path

from ssz import BitList, Boolean, ByteList, List, SSZType, Uint8, Uint64, Uint256, hash_tree_root
from ssz.exceptions import SSZError

# The bytes of one element of each unsigned integer type, as SSZ writes it.
WIDTHS = {Uint8: 1, Uint64: 8, Uint256: 32}


def uint_list(element: type, limit: int) -> type:
    """A list of unsigned integers of one width, with a limit."""
    return type(f"List{WIDTHS[element]}x{limit}", (List[element],), {"LIMIT": limit})


def byte_list(limit: int) -> type:
    """A list of bytes, with a limit."""
    return type(f"ByteList{limit}", (ByteList,), {"LIMIT": limit})


def bitlist(limit: int) -> type:
    """A list of bits, with a limit."""
    return type(f"BitList{limit}", (BitList,), {"LIMIT": limit})


# Each type: its name, its form in the cases, its class, and the reason for its limit.
# A 32-bit or 64-bit product of the limit and the element size wraps to 0 or to a small number.
TYPES = [
    ("list_uint64_2p29", ("list", 8, 2**29), uint_list(Uint64, 2**29), "2^32 bytes"),
    (
        "list_uint64_2p29_plus1",
        ("list", 8, 2**29 + 1),
        uint_list(Uint64, 2**29 + 1),
        "2^32 + 8 bytes",
    ),
    ("list_uint64_2p61", ("list", 8, 2**61), uint_list(Uint64, 2**61), "2^64 bytes"),
    (
        "list_uint64_2p61_plus1",
        ("list", 8, 2**61 + 1),
        uint_list(Uint64, 2**61 + 1),
        "2^64 + 8 bytes",
    ),
    ("list_uint8_2p32", ("list", 1, 2**32), uint_list(Uint8, 2**32), "2^32 bytes"),
    ("list_uint8_2p37", ("list", 1, 2**37), uint_list(Uint8, 2**37), "2^32 chunks"),
    ("list_uint256_2p32", ("list", 32, 2**32), uint_list(Uint256, 2**32), "2^32 chunks"),
    ("list_uint256_2p59", ("list", 32, 2**59), uint_list(Uint256, 2**59), "2^64 bytes"),
    ("list_uint256_2p64", ("list", 32, 2**64), uint_list(Uint256, 2**64), "2^64 chunks"),
    ("byte_list_2p32", ("byte_list", 1, 2**32), byte_list(2**32), "2^32 bytes"),
    ("byte_list_2p64", ("byte_list", 1, 2**64), byte_list(2**64), "2^64 bytes"),
    ("byte_list_2p69", ("byte_list", 1, 2**69), byte_list(2**69), "2^64 chunks"),
    ("bitlist_2p35", ("bitlist", 0, 2**35), bitlist(2**35), "2^32 bytes"),
    ("bitlist_2p40", ("bitlist", 0, 2**40), bitlist(2**40), "2^32 chunks"),
    ("bitlist_2p67", ("bitlist", 0, 2**67), bitlist(2**67), "2^64 bytes"),
    ("bitlist_2p72", ("bitlist", 0, 2**72), bitlist(2**72), "2^64 chunks"),
    (
        "list_uint64_2p64_minus1",
        ("list", 8, 2**64 - 1),
        uint_list(Uint64, 2**64 - 1),
        "the largest 64-bit limit",
    ),
    (
        "list_uint256_2p32_minus1",
        ("list", 32, 2**32 - 1),
        uint_list(Uint256, 2**32 - 1),
        "2^32 - 1 chunks",
    ),
    (
        "list_uint256_2p32_plus1",
        ("list", 32, 2**32 + 1),
        uint_list(Uint256, 2**32 + 1),
        "2^32 + 1 chunks",
    ),
    (
        "list_uint256_2p64_minus1",
        ("list", 32, 2**64 - 1),
        uint_list(Uint256, 2**64 - 1),
        "2^64 - 1 chunks",
    ),
    ("byte_list_2p32_minus1", ("byte_list", 1, 2**32 - 1), byte_list(2**32 - 1), "2^32 - 1 bytes"),
    ("byte_list_2p64_minus1", ("byte_list", 1, 2**64 - 1), byte_list(2**64 - 1), "2^64 - 1 bytes"),
    (
        "bitlist_2p32_minus1",
        ("bitlist", 0, 2**32 - 1),
        bitlist(2**32 - 1),
        "the largest 32-bit limit",
    ),
    (
        "bitlist_2p35_minus1",
        ("bitlist", 0, 2**35 - 1),
        bitlist(2**35 - 1),
        "an encoding of up to 2^32 bytes",
    ),
    (
        "bitlist_2p64_minus1",
        ("bitlist", 0, 2**64 - 1),
        bitlist(2**64 - 1),
        "the largest 64-bit limit",
    ),
]


def values(kind: str, width: int, cls: type) -> dict[str, tuple[list, SSZType]]:
    """The valid values of a type, by case: each as its elements, and as a value of the class."""
    if kind == "bitlist":
        bits = {"empty": [], "three": [True, False, True], "nine": [True] * 9}
        return {case: (b, cls(data=[Boolean(x) for x in b])) for case, b in bits.items()}
    element = {1: Uint8, 8: Uint64, 32: Uint256}[width]
    top = 2 ** (8 * width) - 1
    numbers = {"empty": [], "two": [1, top], "three": [0, 2**53 + 1 if width >= 8 else 7, top]}
    if kind == "byte_list":
        return {case: (n, cls(data=bytes(n))) for case, n in numbers.items()}
    return {case: (n, cls(data=[element(x) for x in n])) for case, n in numbers.items()}


def invalid(kind: str, width: int) -> dict[str, tuple[bytes, str]]:
    """Bytes that no value of a type has, with the reason, by case."""
    if kind == "bitlist":
        # No delimiter bit: an empty input, and a last byte of zero.
        return {"no_bytes": (b"", "empty"), "zero_last_byte": (b"\x05\x00", "no_delimiter")}
    if width == 1:
        # Every length of bytes is a whole number of elements of one byte.
        return {}
    return {
        "one_byte_more": (bytes(2 * width + 1), "partial_element"),
        "one_byte_less": (bytes(width - 1), "partial_element"),
    }


def rejects(cls: type, data: bytes) -> bool:
    """Whether the class rejects the bytes."""
    try:
        cls.decode_bytes(data)
    except SSZError:
        return True
    return False


def main(out: Path) -> None:
    """Write the cases as one JSON file."""
    cases = []
    for name, (kind, width, limit), cls, reason in TYPES:
        for case, (elements, value) in values(kind, width, cls).items():
            data = value.encode_bytes()
            assert cls.decode_bytes(data) == value
            cases.append(
                {
                    "name": f"{name}/{case}",
                    "kind": kind,
                    "width": width,
                    "limit": limit,
                    "limit_reaches": reason,
                    "value": elements,
                    "serialized": "0x" + data.hex(),
                    "root": "0x" + bytes(hash_tree_root(value)).hex(),
                }
            )
        for case, (data, why) in invalid(kind, width).items():
            assert rejects(cls, data), (name, case)
            cases.append(
                {
                    "name": f"{name}/invalid_{case}",
                    "kind": kind,
                    "width": width,
                    "limit": limit,
                    "limit_reaches": reason,
                    "value": None,
                    "serialized": "0x" + data.hex(),
                    "root": None,
                    "reason": why,
                }
            )
    (out / "cases.json").write_text(json.dumps(cases, indent=1) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
