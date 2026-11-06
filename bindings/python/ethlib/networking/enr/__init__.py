"""Ethereum Node Records, from EIP-778, with the "v4" identity scheme."""

from typing import NamedTuple

from ethlib import consensus

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import EnrError
from ethlib.serialization import rlp

# A record is its RLP bytes, at most this many bytes long.
# Its text form is "enr:", then the unpadded URL-safe base64 of those bytes.
#
# Each function decodes the record first.
# A rejected record or a malformed text raises `EnrError`.
# It is a `ValueError` with the code of the Lean error.
MAX_RECORD_SIZE = _native.ENR_MAX_RECORD_SIZE


def from_text(text: str) -> bytes:
    """The RLP bytes of a record in text form."""
    return _native.enr_from_text(text)


def seq(record: bytes) -> int:
    """The sequence number of a record."""
    return _native.enr_seq(record)


def verify_v4(record: bytes) -> bool:
    """
    Whether the record names the "v4" scheme and its signature verifies under its public key.

    A high s is accepted, since EIP-778 adds no low-s rule.
    """
    return _native.enr_verify_v4(record)


def node_id(record: bytes) -> bytes:
    """
    The 32-byte node ID of a "v4" record: the Keccak-256 hash of the x and y of its key.

    It does not check the signature.
    """
    return _native.enr_node_id(record)


class EnrForkId(NamedTuple):
    """The eth2 entry: the fork digest now, and the version and epoch of the next fork."""

    fork_digest: bytes
    next_fork_version: bytes
    next_fork_epoch: int


class ConsensusEntries(NamedTuple):
    """
    The consensus entries of a record, as a node at one fork reads them.

    attnets and syncnets are the SSZ bytes of their bitvectors, or None when absent.

    A node before Altair does not read syncnets, and a node before Fulu does not read cgc or nfd.
    """

    eth2: EnrForkId
    attnets: bytes | None
    syncnets: bytes | None
    cgc: int | None
    nfd: bytes | None


def consensus_entries(fork: str, record: bytes, config: str = "mainnet") -> ConsensusEntries:
    """The consensus entries of a record at a fork, with the subnet count of a configuration."""
    count = consensus.config(config)["ATTESTATION_SUBNET_COUNT"]
    raw = _native.enr_consensus_entries(fork, count, record)
    eth2 = EnrForkId(raw[0:4], raw[4:8], int.from_bytes(raw[8:16], "little"))
    pos = 16
    fields = []
    # attnets: one bit per subnet, syncnets: 1 byte, cgc: a little-endian uint64, nfd: 4 bytes.
    for size in ((count + 7) // 8, 1, 8, 4):
        if raw[pos] == 0:
            fields.append(None)
            pos += 1
        else:
            fields.append(raw[pos + 1 : pos + 1 + size])
            pos += 1 + size
    attnets, syncnets, cgc, nfd = fields
    cgc_value = None if cgc is None else int.from_bytes(cgc, "little")
    return ConsensusEntries(eth2, attnets, syncnets, cgc_value, nfd)


def eth_fork_id(record: bytes) -> tuple[bytes, int] | None:
    """The fork hash and next fork of the "eth" entry of a record, or None without the entry."""
    raw = _native.enr_eth_fork_id(record)
    if not raw:
        return None
    fork_hash, fork_next = rlp.decode(raw)
    return fork_hash, int.from_bytes(fork_next, "big")


__all__ = [
    "MAX_RECORD_SIZE",
    "from_text",
    "seq",
    "verify_v4",
    "node_id",
    "EnrForkId",
    "ConsensusEntries",
    "consensus_entries",
    "eth_fork_id",
    "EnrError",
]
