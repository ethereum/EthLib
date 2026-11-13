"""The gossipsub router on one RPC, against the rules of gossipsub v1.0 and v1.1."""

from dataclasses import replace

import pytest

from ethlib.errors import GossipError
from ethlib.networking import gossip
from ethlib.networking.gossip.router import (
    GossipsubParameters,
    Out,
    RouterState,
    Standing,
    ValidationResult,
    parameters,
    receive_rpc,
)
from ethlib.networking.gossip.rpc import (
    Control,
    Graft,
    IDontWant,
    IHave,
    IWant,
    Message,
    Prune,
    Rpc,
    SubOpts,
)
from raising import raises

# The rules are in libp2p/specs at commit c750236de43cd8b246a824b377dfdb26bae686db.
# Message handling is "Message Processing" of pubsub/gossipsub/gossipsub-v1.0.md.
# The v1.1 rules are six sections of pubsub/gossipsub/gossipsub-v1.1.md.
# The first two are "Extended Validators" and "PRUNE Backoff and Peer Exchange".
# The next two are "Explicit Peering Agreements" and "Outbound Mesh Quotas".
# The last two are "Spam Protection Measures" and "Score Thresholds".
# Neither document publishes vectors, so each case below is built by hand.

FORK = "fusaka"
TOPIC = "/eth2/b5303f2a/beacon_block/ssz_snappy"
OTHER = "/eth2/b5303f2a/voluntary_exit/ssz_snappy"
A, B, C, D, E, X = b"peer-a", b"peer-b", b"peer-c", b"peer-d", b"peer-e", b"peer-x"

# Twelve-second slots and 32 slots per epoch, as on mainnet: the seen lifetime is 768 s.
PARAMS = parameters(12000, 32)
EXTEND_MS = 30_000
PRUNE_MS = 60_000

M = Message(data=b"block", topic=TOPIC)
M_ID = gossip.message_id(FORK, TOPIC.encode(), M.data)
UNSEEN = bytes(range(20))

JOINED = RouterState(topics=(TOPIC,), mesh=((TOPIC, (A, B)),))


def _receive(
    src: bytes,
    rpc: Rpc,
    state: RouterState,
    *,
    now: int = 1_000,
    validation: dict[bytes, ValidationResult] | None = None,
    standing: dict[bytes, Standing] | None = None,
    params: GossipsubParameters | None = None,
    fork: str = FORK,
) -> tuple[RouterState, Out]:
    return receive_rpc(
        fork=fork,
        params=PARAMS if params is None else params,
        backoff_ms=EXTEND_MS,
        prune_backoff_ms=PRUNE_MS,
        standing={} if standing is None else standing,
        validation={M_ID: "accept"} if validation is None else validation,
        now_ms=now,
        src=src,
        rpc=rpc,
        state=state,
    )


def _mesh(state: RouterState, topic: str = TOPIC) -> tuple[bytes, ...]:
    return dict(state.mesh).get(topic, ())


def test_parameters_follow_the_slot() -> None:
    assert PARAMS == GossipsubParameters(
        d=8,
        d_low=6,
        d_high=12,
        d_lazy=6,
        heartbeat_interval_ms=700,
        fanout_ttl=60,
        mcache_len=6,
        mcache_gossip=3,
        seen_ttl=768,
    )


def test_seen_lifetime_drops_the_remainder() -> None:
    # Two epochs of one 1.7 s slot are 3.4 s, so 3 whole seconds.
    assert parameters(1700, 1).seen_ttl == 3


# Every field holds two distinct entries, and the message cache two windows.
OLD = Message(data=b"old", topic=TOPIC)
OLD_ID = gossip.message_id(FORK, TOPIC.encode(), OLD.data)
FULL = RouterState(
    topics=(TOPIC, OTHER),
    peer_topics=((A, (TOPIC, OTHER)), (B, (TOPIC,))),
    mesh=((TOPIC, (A, B)), (OTHER, (C,))),
    fanout=((OTHER, (D, E)), (TOPIC, (C,))),
    backoff=(((TOPIC, D), 9_000), ((OTHER, E), 8_000)),
    outbound=(A, C),
    explicit=(X, b"peer-y"),
    mcache=(((M_ID, M),), ((OLD_ID, OLD), (UNSEEN, M))),
    seen=((M_ID, 900), (OLD_ID, 100)),
)


def test_state_crosses_unchanged() -> None:
    assert _receive(A, Rpc(), FULL) == (FULL, Out())


def test_subscriptions_update_the_topics_of_the_sender() -> None:
    rpc = Rpc(
        subscriptions=(
            SubOpts(subscribe=True, topic_id="/new"),
            SubOpts(subscribe=False, topic_id=TOPIC),
        )
    )
    state, _ = _receive(A, rpc, FULL)
    assert state == replace(FULL, peer_topics=((A, (OTHER, "/new")), (B, (TOPIC,))))


def test_iwant_is_answered_from_an_older_window() -> None:
    iwant = Rpc(control=Control(iwant=(IWant(message_ids=(OLD_ID,)),)))
    assert _receive(E, iwant, FULL)[1] == Out(answers=((E, OLD),))


def test_idontwant_is_ignored() -> None:
    rpc = Rpc(control=Control(idontwant=(IDontWant(message_ids=(M_ID,)),)))
    assert _receive(A, rpc, FULL) == (FULL, Out())


def test_phase0_ids_follow_the_phase0_rule() -> None:
    phase0_id = gossip.message_id("phase0", TOPIC.encode(), M.data)
    assert phase0_id != M_ID
    state, out = _receive(
        A, Rpc(publish=(M,)), JOINED, fork="phase0", validation={phase0_id: "accept"}
    )
    assert out.delivered == (M,)
    assert state.seen == ((phase0_id, 1_000),)


def test_accepted_message_is_delivered_cached_and_forwarded_to_the_mesh() -> None:
    state, out = _receive(A, Rpc(publish=(M,)), JOINED)
    assert out == Out(forward=((A, M), (B, M)), delivered=(M,))
    assert state.seen == ((M_ID, 1_000),)
    assert state.mcache == (((M_ID, M),),)


def test_seen_message_is_neither_validated_nor_forwarded() -> None:
    state, _ = _receive(A, Rpc(publish=(M,)), JOINED)
    # B's copy would be rejected, but the seen cache stops it before validation.
    again, out = _receive(B, Rpc(publish=(M,)), state, validation={M_ID: ("reject", "bad")})
    assert out == Out()
    assert again == state


def test_seen_entry_expires_after_its_lifetime() -> None:
    state, _ = _receive(A, Rpc(publish=(M,)), JOINED)
    lifetime = PARAMS.seen_ttl * 1000
    _, inside = _receive(B, Rpc(publish=(M,)), state, now=1_000 + lifetime - 1)
    _, after = _receive(B, Rpc(publish=(M,)), state, now=1_000 + lifetime)
    assert inside == Out()
    assert after.delivered == (M,)


@pytest.mark.parametrize("result", [("ignore", "late"), ("reject", "bad signature")])
def test_message_not_accepted_is_neither_delivered_nor_forwarded(
    result: ValidationResult,
) -> None:
    state, out = _receive(A, Rpc(publish=(M,)), JOINED, validation={M_ID: result})
    assert out == Out()
    # Its ID stays in the seen cache, and the message cache stays empty.
    assert state.seen == ((M_ID, 1_000),)
    assert state.mcache == ((),)


def test_message_without_validation_result_is_ignored() -> None:
    state, out = _receive(A, Rpc(publish=(M,)), JOINED, validation={})
    assert out == Out()
    assert state.seen == ((M_ID, 1_000),)


def test_message_on_unjoined_topic_is_dropped_before_the_seen_cache() -> None:
    other = Message(data=M.data, topic=OTHER)
    other_id = gossip.message_id(FORK, OTHER.encode(), M.data)
    state, out = _receive(A, Rpc(publish=(other,)), JOINED, validation={other_id: "accept"})
    assert out == Out()
    assert state == JOINED


def test_graft_below_high_bound_joins_the_mesh() -> None:
    state, out = _receive(C, Rpc(control=Control(graft=(Graft(topic_id=TOPIC),))), JOINED)
    assert _mesh(state) == (A, B, C)
    assert out == Out()


def test_graft_within_backoff_gets_prune_and_extends_backoff() -> None:
    # D prunes at t = 0 with a backoff of 60 s, then grafts 10 s later.
    prune = Rpc(control=Control(prune=(Prune(topic_id=TOPIC, backoff=60),)))
    state, _ = _receive(D, prune, JOINED, now=0)
    assert state.backoff == (((TOPIC, D), 60_000),)
    graft = Rpc(control=Control(graft=(Graft(topic_id=TOPIC),)))
    state, out = _receive(D, graft, state, now=10_000)
    assert _mesh(state) == (A, B)
    assert state.backoff == (((TOPIC, D), 60_000 + EXTEND_MS),)
    # What remains: 60 s + 30 s - 10 s, in whole seconds.
    assert out == Out(control=((D, Control(prune=(Prune(topic_id=TOPIC, backoff=80),))),))


def test_remaining_backoff_rounds_up() -> None:
    # 4.5 s + 30 s - 1 s leaves 33.5 s, which the PRUNE carries as 34 s.
    state = replace(JOINED, backoff=(((TOPIC, C), 4_500),))
    _, out = _receive(C, Rpc(control=Control(graft=(Graft(topic_id=TOPIC),))), state)
    assert out.control == ((C, Control(prune=(Prune(topic_id=TOPIC, backoff=34),))),)


def test_prune_never_shortens_a_backoff() -> None:
    state = replace(JOINED, backoff=(((TOPIC, A), 500_000),))
    prune = Rpc(control=Control(prune=(Prune(topic_id=TOPIC, backoff=1),)))
    after, _ = _receive(A, prune, state)
    assert after.backoff == (((TOPIC, A), 500_000),)


def test_prune_on_unjoined_topic_is_ignored() -> None:
    prune = Rpc(control=Control(prune=(Prune(topic_id=OTHER, backoff=60),)))
    assert _receive(A, prune, JOINED) == (JOINED, Out())


def test_graft_within_backoff_removes_a_mesh_peer() -> None:
    state = replace(JOINED, backoff=(((TOPIC, A), 5_000),))
    state, out = _receive(A, Rpc(control=Control(graft=(Graft(topic_id=TOPIC),))), state)
    assert _mesh(state) == (B,)
    assert out.control == ((A, Control(prune=(Prune(topic_id=TOPIC, backoff=34),))),)


def test_prune_without_backoff_takes_the_default() -> None:
    state, _ = _receive(A, Rpc(control=Control(prune=(Prune(topic_id=TOPIC),))), JOINED)
    assert _mesh(state) == (B,)
    assert state.backoff == (((TOPIC, A), 1_000 + PRUNE_MS),)


def test_graft_on_unjoined_topic_is_ignored() -> None:
    state, out = _receive(C, Rpc(control=Control(graft=(Graft(topic_id=OTHER),))), JOINED)
    assert state == JOINED
    assert out == Out()


def test_full_mesh_admits_only_outbound_peers() -> None:
    params = replace(PARAMS, d_high=2)
    graft = Rpc(control=Control(graft=(Graft(topic_id=TOPIC),)))
    inbound, out = _receive(C, graft, JOINED, params=params)
    assert _mesh(inbound) == (A, B)
    assert out == Out()
    outbound, _ = _receive(C, graft, replace(JOINED, outbound=(C,)), params=params)
    assert _mesh(outbound) == (A, B, C)


def test_explicit_peer_is_pruned_and_gets_every_message() -> None:
    state = replace(JOINED, explicit=(X,))
    graft = Rpc(control=Control(graft=(Graft(topic_id=TOPIC),)))
    after, out = _receive(X, graft, state)
    assert _mesh(after) == (A, B)
    assert out.control == ((X, Control(prune=(Prune(topic_id=TOPIC, backoff=0),))),)
    _, out = _receive(A, Rpc(publish=(M,)), state)
    assert out.forward == ((A, M), (B, M), (X, M))


def test_graylisted_peer_changes_nothing() -> None:
    rpc = Rpc(publish=(M,), control=Control(graft=(Graft(topic_id=TOPIC),)))
    state, out = _receive(C, rpc, JOINED, standing={C: Standing(below_graylist=True)})
    assert state == JOINED
    assert out == Out()


def test_explicit_peer_is_never_graylisted() -> None:
    state = replace(JOINED, explicit=(X,))
    _, out = _receive(X, Rpc(publish=(M,)), state, standing={X: Standing(below_graylist=True)})
    assert out.delivered == (M,)


def test_ihave_asks_for_unseen_ids() -> None:
    state, _ = _receive(A, Rpc(publish=(M,)), JOINED)
    ihave = Rpc(control=Control(ihave=(IHave(topic_id=TOPIC, message_ids=(M_ID, UNSEEN)),)))
    _, out = _receive(E, ihave, state)
    assert out == Out(control=((E, Control(iwant=(IWant(message_ids=(UNSEEN,)),))),))


def test_ihave_with_short_id_or_unjoined_topic_asks_nothing() -> None:
    short = Rpc(control=Control(ihave=(IHave(topic_id=TOPIC, message_ids=(b"\x01" * 19,)),)))
    other = Rpc(control=Control(ihave=(IHave(topic_id=OTHER, message_ids=(UNSEEN,)),)))
    assert _receive(E, short, JOINED)[1] == Out()
    assert _receive(E, other, JOINED)[1] == Out()


def test_iwant_is_answered_from_the_message_cache() -> None:
    state, _ = _receive(A, Rpc(publish=(M,)), JOINED)
    iwant = Rpc(control=Control(iwant=(IWant(message_ids=(M_ID, UNSEEN)),)))
    _, out = _receive(E, iwant, state)
    assert out == Out(answers=((E, M),))


def test_gossip_below_threshold_is_ignored() -> None:
    state, _ = _receive(A, Rpc(publish=(M,)), JOINED)
    rpc = Rpc(
        control=Control(
            ihave=(IHave(topic_id=TOPIC, message_ids=(UNSEEN,)),),
            iwant=(IWant(message_ids=(M_ID,)),),
        )
    )
    _, out = _receive(E, rpc, state, standing={E: Standing(below_gossip=True)})
    assert out == Out()


def test_explicit_peer_below_gossip_threshold_gets_gossip() -> None:
    state, _ = _receive(A, Rpc(publish=(M,)), replace(JOINED, explicit=(X,)))
    rpc = Rpc(control=Control(iwant=(IWant(message_ids=(M_ID,)),)))
    _, out = _receive(X, rpc, state, standing={X: Standing(below_gossip=True)})
    assert out == Out(answers=((X, M),))


def test_short_validation_key_is_rejected() -> None:
    with raises(GossipError, "expected 20 bytes, got 19"):
        _receive(A, Rpc(), JOINED, validation={bytes(19): "accept"})


def test_unknown_validation_result_is_rejected() -> None:
    # A verdict that no constructor names, on purpose.
    bad: ValidationResult = ("maybe", "?")  # ty: ignore[invalid-assignment]
    with raises(GossipError, "no constructor is named maybe"):
        _receive(A, Rpc(), JOINED, validation={M_ID: bad})


def test_unknown_fork_is_rejected() -> None:
    with raises(GossipError, "no fork named nofork"):
        receive_rpc(
            fork="nofork",
            params=PARAMS,
            backoff_ms=EXTEND_MS,
            prune_backoff_ms=PRUNE_MS,
            standing={},
            validation={},
            now_ms=0,
            src=A,
            rpc=Rpc(),
            state=JOINED,
        )
