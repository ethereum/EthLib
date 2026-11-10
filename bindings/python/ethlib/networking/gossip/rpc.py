"""The gossipsub RPC that carries consensus gossip, under the StrictNoSign policy."""

from dataclasses import asdict, dataclass, field
from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import GossipError as GossipError


@dataclass(frozen=True, slots=True, kw_only=True)
class SubOpts:
    """A subscription change: subscribe to a topic, or unsubscribe from it."""

    subscribe: bool = False
    topic_id: str = ""


@dataclass(frozen=True, slots=True, kw_only=True)
class Message:
    """A published message: its data and its topic."""

    data: bytes = b""
    topic: str


@dataclass(frozen=True, slots=True, kw_only=True)
class IHave:
    """IHAVE: the IDs of messages the sender has seen on a topic."""

    topic_id: str = ""
    message_ids: tuple[bytes, ...] = ()


@dataclass(frozen=True, slots=True, kw_only=True)
class IWant:
    """IWANT: the IDs of messages the sender asks for."""

    message_ids: tuple[bytes, ...] = ()


@dataclass(frozen=True, slots=True, kw_only=True)
class Graft:
    """GRAFT: the sender added the receiver to its mesh of a topic."""

    topic_id: str = ""


@dataclass(frozen=True, slots=True, kw_only=True)
class PeerInfo:
    """A peer offered in a PRUNE, with its signed peer record when the sender has one."""

    peer_id: bytes = b""
    signed_peer_record: bytes = b""


@dataclass(frozen=True, slots=True, kw_only=True)
class Prune:
    """PRUNE: the sender left the mesh of a topic; backoff is the seconds before a new GRAFT."""

    topic_id: str = ""
    peers: tuple[PeerInfo, ...] = ()
    backoff: int = 0


@dataclass(frozen=True, slots=True, kw_only=True)
class IDontWant:
    """IDONTWANT: the IDs of messages the sender does not want to receive."""

    message_ids: tuple[bytes, ...] = ()


@dataclass(frozen=True, slots=True, kw_only=True)
class Control:
    """The control messages of one RPC."""

    ihave: tuple[IHave, ...] = ()
    iwant: tuple[IWant, ...] = ()
    graft: tuple[Graft, ...] = ()
    prune: tuple[Prune, ...] = ()
    idontwant: tuple[IDontWant, ...] = ()


@dataclass(frozen=True, slots=True, kw_only=True)
class Rpc:
    """One RPC: subscription changes, published messages and control messages."""

    subscriptions: tuple[SubOpts, ...] = ()
    publish: tuple[Message, ...] = ()
    control: Control = field(default_factory=Control)


def _control(value: dict[str, Any]) -> Control:
    return Control(
        ihave=tuple(
            IHave(topic_id=m["topic_id"], message_ids=tuple(m["message_ids"]))
            for m in value["ihave"]
        ),
        iwant=tuple(IWant(message_ids=tuple(m["message_ids"])) for m in value["iwant"]),
        graft=tuple(Graft(topic_id=m["topic_id"]) for m in value["graft"]),
        prune=tuple(
            Prune(
                topic_id=m["topic_id"],
                peers=tuple(
                    PeerInfo(peer_id=p["peer_id"], signed_peer_record=p["signed_peer_record"])
                    for p in m["peers"]
                ),
                backoff=m["backoff"],
            )
            for m in value["prune"]
        ),
        idontwant=tuple(IDontWant(message_ids=tuple(m["message_ids"])) for m in value["idontwant"]),
    )


def decode(data: bytes) -> Rpc:
    """The RPC that the bytes encode; a rejected RPC raises GossipError."""
    # The native dict keys are the Lean field names in snake case; its lists become tuples here.
    value = _native.gossip_rpc_decode(data)
    return Rpc(
        subscriptions=tuple(
            SubOpts(subscribe=s["subscribe"], topic_id=s["topic_id"])
            for s in value["subscriptions"]
        ),
        publish=tuple(Message(data=m["data"], topic=m["topic"]) for m in value["publish"]),
        control=_control(value["control"]),
    )


def encode(rpc: Rpc) -> bytes:
    """The bytes of an RPC; a value out of range for its field raises GossipError or ValueError."""
    # The native dict keys are the Lean field names in snake case, which are the names here.
    return _native.gossip_rpc_encode(asdict(rpc))


__all__ = [
    "Control",
    "GossipError",
    "Graft",
    "IDontWant",
    "IHave",
    "IWant",
    "Message",
    "PeerInfo",
    "Prune",
    "Rpc",
    "SubOpts",
    "decode",
    "encode",
]
