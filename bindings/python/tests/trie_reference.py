"""A reference Merkle Patricia trie over 32-byte keys, with its root and the proof of each key."""

# It is written apart from EthLib's trie and follows Appendix D of the Yellow Paper.
# It shares only Keccak-256 and RLP with EthLib, which have their own vector suites.
# Each key is already a 32-byte hash, so the trie does not hash it again.

from typing import TypeAlias

from ethlib.cryptography import keccak
from ethlib.serialization import rlp

# A node as its parent holds it: the RLP structure of a short node, or the hash of a long one.
Node: TypeAlias = "bytes | list[Node]"


def nibbles(key: bytes) -> list[int]:
    """The path of a key: its nibbles, high nibble first."""
    return [n for byte in key for n in (byte >> 4, byte & 0xF)]


def _compact(path: list[int], leaf: bool) -> bytes:
    """The hex-prefix encoding of a path, HP of Appendix C."""
    flag = 2 * leaf + len(path) % 2
    padded = [flag] + ([] if len(path) % 2 else [0]) + path
    return bytes(16 * high + low for high, low in zip(padded[::2], padded[1::2], strict=True))


def _shared(paths: list[list[int]], level: int) -> int:
    """The number of nibbles after `level` that every path shares."""
    length = len(paths[0]) - level
    for path in paths[1:]:
        n = 0
        while n < length and path[level + n] == paths[0][level + n]:
            n += 1
        length = n
    return length


class Trie:
    """A trie of 32-byte keys, with the encoding of every node that its parent holds by hash."""

    def __init__(self, pairs: dict[bytes, bytes]) -> None:
        self._pairs = pairs
        self._paths = {key: nibbles(key) for key in pairs}
        self._nodes: dict[bytes, bytes] = {}
        # The root is the hash of the root node's encoding, even when it is short.
        encoded = rlp.encode(self._build(sorted(pairs), 0))
        self.root = keccak.keccak256(encoded)
        self._nodes[self.root] = encoded

    def _held(self, node: Node) -> Node:
        encoded = rlp.encode(node)
        if len(encoded) < 32:
            return node
        digest = keccak.keccak256(encoded)
        self._nodes[digest] = encoded
        return digest

    def _build(self, keys: list[bytes], level: int) -> Node:
        if not keys:
            return b""
        paths = [self._paths[key] for key in keys]
        if len(keys) == 1:
            return [_compact(paths[0][level:], True), self._pairs[keys[0]]]
        shared = _shared(paths, level)
        if shared:
            child = self._held(self._build(keys, level + shared))
            return [_compact(paths[0][level : level + shared], False), child]
        # Every key has 64 nibbles, so no key ends at a branch and its value is empty.
        children = [
            self._held(self._build([k for k in keys if self._paths[k][level] == n], level + 1))
            for n in range(16)
        ]
        return [*children, b""]

    def proof(self, key: bytes) -> list[bytes]:
        """The encodings of the root node and of each node on the path of `key` held by hash."""
        path, out = nibbles(key), []
        node: Node = self.root
        while True:
            if isinstance(node, bytes):
                if not node:
                    return out
                out.append(self._nodes[node])
                node = rlp.decode(self._nodes[node])
                # The root of the empty trie is the encoding of the empty string.
                if not node:
                    return out
            if len(node) == 17:
                node, path = node[path[0]], path[1:]
                continue
            # A leaf or an extension: its path follows the flag nibble and its padding.
            compact = nibbles(node[0])
            segment = compact[2 - compact[0] % 2 :]
            if compact[0] >= 2 or path[: len(segment)] != segment:
                return out
            node, path = node[1], path[len(segment) :]
