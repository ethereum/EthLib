"""The gossipsub router on one received RPC, with every client choice passed in."""

from collections.abc import Mapping
from dataclasses import asdict, dataclass
from typing import Any, Literal, TypeAlias

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import GossipError as GossipError

# The converters of the RPC module are private to the package, which this module is part of.
from ethlib.networking.gossip.rpc import Control, Message, Rpc, _control, _message

# A validation result: accepted, or ignored or rejected with a reason.
# The package supports Python 3.10, which has no `type` statement.
ValidationResult: TypeAlias = Literal["accept"] | tuple[Literal["ignore", "reject"], str]


@dataclass(frozen=True, slots=True, kw_only=True)
class GossipsubParameters:
    """The gossipsub parameters of the consensus layer, with times in milliseconds or seconds."""

    d: int
    d_low: int
    d_high: int
    d_lazy: int
    heartbeat_interval_ms: int
    fanout_ttl: int
    mcache_len: int
    mcache_gossip: int
    seen_ttl: int


@dataclass(frozen=True, slots=True, kw_only=True)
class Standing:
    """What the router reads of the score of a peer: below zero, and below three thresholds."""

    negative: bool = False
    below_gossip: bool = False
    below_publish: bool = False
    below_graylist: bool = False


@dataclass(frozen=True, slots=True, kw_only=True)
class RouterState:
    """The state of a router; the caches hold message IDs of 20 bytes and times in milliseconds."""

    topics: tuple[str, ...] = ()
    peer_topics: tuple[tuple[bytes, tuple[str, ...]], ...] = ()
    mesh: tuple[tuple[str, tuple[bytes, ...]], ...] = ()
    fanout: tuple[tuple[str, tuple[bytes, ...]], ...] = ()
    backoff: tuple[tuple[tuple[str, bytes], int], ...] = ()
    outbound: tuple[bytes, ...] = ()
    explicit: tuple[bytes, ...] = ()
    mcache: tuple[tuple[tuple[bytes, Message], ...], ...] = ((),)
    seen: tuple[tuple[bytes, int], ...] = ()


@dataclass(frozen=True, slots=True, kw_only=True)
class Out:
    """What the router sends and delivers on one RPC, each list in the order it was produced."""

    forward: tuple[tuple[bytes, Message], ...] = ()
    answers: tuple[tuple[bytes, Message], ...] = ()
    control: tuple[tuple[bytes, Control], ...] = ()
    delivered: tuple[Message, ...] = ()


# The native keys of the four mesh degrees: the Lean fields D to D_lazy in snake case.
_DEGREE_KEYS = {"d": "_d", "d_low": "_d_low", "d_high": "_d_high", "d_lazy": "_d_lazy"}


def parameters(slot_duration_ms: int, slots_per_epoch: int) -> GossipsubParameters:
    """The gossipsub parameters, given the slot duration in milliseconds and the slots per epoch."""
    value = _native.gossip_parameters(slot_duration_ms, slots_per_epoch)
    for name, key in _DEGREE_KEYS.items():
        value[name] = value.pop(key)
    return GossipsubParameters(**value)


def _params_value(params: GossipsubParameters) -> dict[str, int]:
    value = asdict(params)
    for name, key in _DEGREE_KEYS.items():
        value[key] = value.pop(name)
    return value


def _state_value(state: RouterState) -> dict[str, Any]:
    # The native dict keys are the Lean field names in snake case.
    # The two caches are structures there, with one field each.
    value = asdict(state)
    value["mcache"] = {"windows": value["mcache"]}
    value["seen"] = {"entries": value["seen"]}
    return value


def _state(value: dict[str, Any]) -> RouterState:
    return RouterState(
        topics=tuple(value["topics"]),
        peer_topics=tuple((peer, tuple(topics)) for peer, topics in value["peer_topics"]),
        mesh=tuple((topic, tuple(peers)) for topic, peers in value["mesh"]),
        fanout=tuple((topic, tuple(peers)) for topic, peers in value["fanout"]),
        backoff=tuple(((topic, peer), end) for (topic, peer), end in value["backoff"]),
        outbound=tuple(value["outbound"]),
        explicit=tuple(value["explicit"]),
        mcache=tuple(
            tuple((id_, _message(m)) for id_, m in window) for window in value["mcache"]["windows"]
        ),
        seen=tuple((id_, time) for id_, time in value["seen"]["entries"]),
    )


def _out(value: dict[str, Any]) -> Out:
    return Out(
        forward=tuple((peer, _message(m)) for peer, m in value["forward"]),
        answers=tuple((peer, _message(m)) for peer, m in value["answers"]),
        control=tuple((peer, _control(c)) for peer, c in value["control"]),
        delivered=tuple(_message(m) for m in value["delivered"]),
    )


def receive_rpc(
    *,
    fork: str,
    params: GossipsubParameters,
    backoff_ms: int,
    prune_backoff_ms: int,
    standing: Mapping[bytes, Standing],
    validation: Mapping[bytes, ValidationResult],
    now_ms: int,
    src: bytes,
    rpc: Rpc,
    state: RouterState,
) -> tuple[RouterState, Out]:
    """The state after one RPC from a peer, and what the router sends and delivers."""
    # The fork names the rule of every message ID, whatever the digest of the topic.
    # A peer missing from the standing has every flag false.
    # A message whose ID is missing from the validation is ignored.
    new_state, out = _native.gossip_receive_rpc(
        fork,
        _params_value(params),
        backoff_ms,
        prune_backoff_ms,
        [(peer, asdict(s)) for peer, s in standing.items()],
        list(validation.items()),
        now_ms,
        src,
        asdict(rpc),
        _state_value(state),
    )
    return _state(new_state), _out(out)


__all__ = [
    "GossipError",
    "GossipsubParameters",
    "Out",
    "RouterState",
    "Standing",
    "ValidationResult",
    "parameters",
    "receive_rpc",
]
