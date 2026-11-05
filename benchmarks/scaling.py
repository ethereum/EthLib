"""How the time of an EthLib call grows with the size of its input."""

# python scaling.py [hash,rlp,trie,snappy,ssz]
#
# Each line gives the times at four or five sizes and the growth exponent between the last two:
# near 1 for a linear operation, near 2 for a quadratic one.

import hashlib
import math
import sys
import time

from ethlib.cryptography import _native as N
from ethlib.cryptography import keccak, sha256
from ethlib.execution import trie
from ethlib.networking import snappy
from ethlib.serialization import rlp, ssz

WHICH = set(sys.argv[1].split(",")) if len(sys.argv) > 1 else None


def t(fn, reps=3):
    """The best time of `reps` calls."""
    best = 1e9
    for _ in range(reps):
        s = time.perf_counter()
        fn()
        best = min(best, time.perf_counter() - s)
    return best


def h(b):
    """SHA-256 of a byte string."""
    return hashlib.sha256(b).digest()


def show(name, sizes, times):
    """Print the times and the growth exponent between the last two sizes."""
    row = "  ".join(f"{n}:{x * 1e3:.3f}ms" for n, x in zip(sizes, times))
    k = (
        math.log(times[-1] / times[-2]) / math.log(sizes[-1] / sizes[-2])
        if times[-2] > 0
        else float("nan")
    )
    print(f"{name:34} {row}   exponent~{k:.2f}", flush=True)


def want(n):
    """Whether the command line asks for the probe `n`."""
    return WHICH is None or n in WHICH


def far_copies(data):
    """A Snappy block of `data` as a literal, then copies of 4 bytes, each `len(data)` bytes back."""
    n = len(data)

    def varint(v):
        return bytes([v & 0x7F | 0x80]) + varint(v >> 7) if v >= 0x80 else bytes([v])

    # format_description.txt §2.2.3: a copy of 4 bytes with a 4-byte offset has the tag 0b00001111.
    copy = bytes([0x0F]) + n.to_bytes(4, "little")
    copies = n // 4
    literal = snappy.compress_literal(data)[len(varint(n)) :]
    return varint(n + 4 * copies) + literal + copy * copies


if want("hash"):
    for name, f in [("keccak", keccak.keccak256), ("sha256", sha256.sha256)]:
        sizes = [1_000, 10_000, 100_000, 1_000_000]
        show(name, sizes, [t(lambda n=n: f(bytes(n))) for n in sizes])

if want("rlp"):
    sizes = [100, 200, 400, 800, 1600]
    show(
        "rlp.decode list of n x 400B",
        sizes,
        [t(lambda d=rlp.encode([bytes(400)] * n): rlp.decode(d)) for n in sizes],
    )
    show(
        "rlp.encode list of n x 400B",
        sizes,
        [t(lambda it=[bytes(400)] * n: rlp.encode(it)) for n in sizes],
    )
    show(
        "rlp.decode one string of n*400B",
        sizes,
        [t(lambda d=rlp.encode(bytes(400 * n)): rlp.decode(d)) for n in sizes],
    )

if want("trie"):
    sizes = [125, 250, 500, 1000]
    pairs = {n: [(h(b"k%d" % i), h(b"v%d" % i)) for i in range(n)] for n in sizes}
    show("trie.root n pairs", sizes, [t(lambda p=pairs[n]: trie.root(p, False), 2) for n in sizes])
    show(
        "  rlp.decode of the same input",
        sizes,
        [t(lambda d=rlp.encode([[k, v] for k, v in pairs[n]]): rlp.decode(d)) for n in sizes],
    )

if want("snappy"):
    sizes = [12_500, 25_000, 50_000, 100_000]
    raw = b"".join(
        b'{"slot":%d,"root":"%s"},' % (i, h(bytes([i % 7])).hex().encode()) for i in range(2000)
    )
    try:
        import snappy as ps

        show(
            "snappy.decompress (real)",
            sizes,
            [t(lambda c=ps.compress(raw[:n]): snappy.decompress(c)) for n in sizes],
        )
    except ImportError:
        pass
    show(
        "snappy.decompress (literal)",
        sizes,
        [t(lambda c=snappy.compress_literal(raw[:n]): snappy.decompress(c)) for n in sizes],
    )
    show(
        "snappy.decompress (far copies)",
        sizes,
        [t(lambda c=far_copies(raw[:n]): snappy.decompress(c)) for n in sizes],
    )
    show(
        "snappy.compress_literal",
        sizes,
        [t(lambda d=raw[:n]: snappy.compress_literal(d)) for n in sizes],
    )

if want("ssz"):
    sizes = [250, 500, 1000, 2000]
    T = {"list": [{"uint": 8}, 2**40]}
    docs = {n: (ssz._dump(T), ssz._dump({"seq": [{"uint": i} for i in range(n)]})) for n in sizes}
    show(
        "ssz serialize List[uint64] n",
        sizes,
        [t(lambda d=docs[n]: N.ssz_serialize(*d)) for n in sizes],
    )
    by = {n: ssz.serialize(T, {"seq": [{"uint": i} for i in range(n)]}) for n in sizes}
    show(
        "ssz deserialize List[uint64] n",
        sizes,
        [t(lambda n=n: N.ssz_deserialize(docs[n][0], by[n])) for n in sizes],
    )
    TB = {"byte_list": 2**30}
    docsb = {n: (ssz._dump(TB), ssz._dump({"bytes": "0x" + bytes(8 * n).hex()})) for n in sizes}
    show(
        "ssz serialize ByteList 8n",
        sizes,
        [t(lambda d=docsb[n]: N.ssz_serialize(*d)) for n in sizes],
    )
    V = {
        "container": [
            ["pubkey", {"byte_vector": 48}],
            ["wc", {"byte_vector": 32}],
            ["eb", {"uint": 8}],
            ["slashed", "bool"],
            ["a", {"uint": 8}],
            ["b", {"uint": 8}],
            ["c", {"uint": 8}],
            ["d", {"uint": 8}],
        ]
    }
    VL = {"list": [V, 2**40]}
    val = {
        "seq": [
            {"bytes": "0x" + bytes(48).hex()},
            {"bytes": "0x" + bytes(32).hex()},
            {"uint": 1},
            {"bool": False},
            {"uint": 1},
            {"uint": 2},
            {"uint": 3},
            {"uint": 4},
        ]
    }
    sizes2 = [125, 250, 500, 1000]
    docsv = {n: (ssz._dump(VL), ssz._dump({"seq": [val] * n})) for n in sizes2}
    show(
        "ssz serialize List[Validator] n",
        sizes2,
        [t(lambda d=docsv[n]: N.ssz_serialize(*d), 1) for n in sizes2],
    )
