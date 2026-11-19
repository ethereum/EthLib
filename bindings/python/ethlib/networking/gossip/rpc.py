"""The gossipsub RPC that carries consensus gossip, under the StrictNoSign policy."""

from dataclasses import asdict, dataclass, field
from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import GossipError as GossipError


@dataclass(frozen=True, slots=True, kw_only=True)
class SubOpts:
    """A subscription change, with the partial message flags that count only in a subscription."""

    subscribe: bool = False
    topic_id: str = ""
    requests_partial: bool = False
    supports_sending_partial: bool = False


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
class ControlExtensions:
    """The extensions that the sender supports, from gossipsub v1.3."""

    partial_messages: bool = False


@dataclass(frozen=True, slots=True, kw_only=True)
class Control:
    """The control messages of one RPC."""

    ihave: tuple[IHave, ...] = ()
    iwant: tuple[IWant, ...] = ()
    graft: tuple[Graft, ...] = ()
    prune: tuple[Prune, ...] = ()
    idontwant: tuple[IDontWant, ...] = ()
    extensions: ControlExtensions | None = None


@dataclass(frozen=True, slots=True, kw_only=True)
class PartialMessagesExtension:
    """A partial message: a part of a full message, or the parts the sender has and wants."""

    topic_id: bytes = b""
    group_id: bytes = b""
    partial_message: bytes | None = None
    parts_metadata: bytes | None = None


@dataclass(frozen=True, slots=True, kw_only=True)
class Rpc:
    """One RPC: subscription changes, published, control and partial messages."""

    subscriptions: tuple[SubOpts, ...] = ()
    publish: tuple[Message, ...] = ()
    control: Control = field(default_factory=Control)
    # The field `partial` of the schema, named as in Lean, where `partial` is a keyword.
    partial_message: PartialMessagesExtension | None = None


def _message(value: dict[str, Any]) -> Message:
    return Message(data=value["data"], topic=value["topic"])


def _extensions(value: dict[str, Any] | None) -> ControlExtensions | None:
    if value is None:
        return None
    return ControlExtensions(partial_messages=value["partial_messages"])


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
        extensions=_extensions(value["extensions"]),
    )


def _partial(value: dict[str, Any] | None) -> PartialMessagesExtension | None:
    if value is None:
        return None
    return PartialMessagesExtension(
        topic_id=value["topic_id"],
        group_id=value["group_id"],
        partial_message=value["partial_message"],
        parts_metadata=value["parts_metadata"],
    )


def decode(data: bytes) -> Rpc:
    """The RPC that the bytes encode; a rejected RPC raises GossipError."""
    # The native dict keys are the Lean field names in snake case; its lists become tuples here.
    value = _native.gossip_rpc_decode(data)
    return Rpc(
        subscriptions=tuple(
            SubOpts(
                subscribe=s["subscribe"],
                topic_id=s["topic_id"],
                requests_partial=s["requests_partial"],
                supports_sending_partial=s["supports_sending_partial"],
            )
            for s in value["subscriptions"]
        ),
        publish=tuple(_message(m) for m in value["publish"]),
        control=_control(value["control"]),
        partial_message=_partial(value["partial_message"]),
    )


def encode(rpc: Rpc) -> bytes:
    """The bytes of an RPC; a value out of range for its field raises GossipError or ValueError."""
    # The native dict keys are the Lean field names in snake case, which are the names here.
    return _native.gossip_rpc_encode(asdict(rpc))


__all__ = [
    "Control",
    "ControlExtensions",
    "GossipError",
    "Graft",
    "IDontWant",
    "IHave",
    "IWant",
    "Message",
    "PartialMessagesExtension",
    "PeerInfo",
    "Prune",
    "Rpc",
    "SubOpts",
    "decode",
    "encode",
]
