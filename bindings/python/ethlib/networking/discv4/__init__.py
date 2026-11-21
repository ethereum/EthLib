"""The packets of the Node Discovery Protocol v4."""

from typing import NamedTuple

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import Discv4Error


def decode(packet: bytes) -> bytes:
    """The hash, the sender's 64-byte key and the content of the packet `packet`."""
    return _native.discv4_decode(packet)


def encode(key: bytes, content: bytes) -> bytes:
    """The packet with the content `content`, packet type then data, signed with `key`."""
    return _native.discv4_encode(key, content)


def record_signed_by(sender: bytes, record: bytes) -> bool:
    """Whether the RLP node record `record` is a valid "v4" record of the key `sender`."""
    return _native.discv4_record_signed_by(sender, record)


class Peer(NamedTuple):
    """What a node knows of an address: its last Ping hash, and the time of the matching Pong."""

    last_ping: bytes | None
    last_pong: int | None


def receive(
    now: int,
    ip: bytes,
    port: int,
    peer: Peer,
    packet: bytes,
    expiration: int,
    enr_seq: int | None,
    record: bytes,
    nodes: bytes,
) -> tuple[Peer, list[bytes]]:
    """
    What a node knows of a packet's sender after it, and the contents of the packets it sends back.

    The node answers with the expiration, sequence number, record and RLP list of nodes given.
    """
    after, replies = _native.discv4_receive(
        now, ip, port, peer.last_ping, peer.last_pong, packet, expiration, enr_seq, record, nodes
    )
    return Peer(*after), replies


def accept_enr_response(request: bytes, response: bytes) -> bool:
    """Whether an ENRResponse packet holds the request's hash and a record of its own signer."""
    return _native.discv4_accept_enr_response(request, response)


__all__ = [
    "Discv4Error",
    "Peer",
    "accept_enr_response",
    "decode",
    "encode",
    "receive",
    "record_signed_by",
]
