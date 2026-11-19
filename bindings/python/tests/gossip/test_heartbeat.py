"""The gossipsub heartbeat, topic membership and publishing, against gossipsub v1.0 and v1.1."""

from dataclasses import replace

import pytest

from ethlib.errors import GossipError
from ethlib.networking import gossip
from ethlib.networking.gossip.router import (
    ClientChoices,
    Out,
    RouterState,
    Standing,
    heartbeat,
    join,
    leave,
    parameters,
    publish,
    receive_rpc,
)
from ethlib.networking.gossip.rpc import Control, Graft, IHave, Message, Prune, Rpc
from raising import raises

# The rules are in libp2p/specs at commit c750236de43cd8b246a824b377dfdb26bae686db.
# Membership, publishing and the heartbeat are three sections of pubsub/gossipsub/gossipsub-v1.0.md.
# They are "Topic Membership", the last list of "Message Processing", and "Heartbeat".
# The v1.1 rules are four sections of gossipsub-v1.1.md.
# They are "Heartbeat Maintenance" and "Outbound Mesh Quotas".
# The others are "Adaptive Gossip Dissemination" and "Flood Publishing".
# Neither document publishes vectors, so each case below is built by hand.
# The exports choose the first candidates, in the order of the candidate list.

FORK = "fusaka"
TOPIC = "/eth2/b5303f2a/beacon_block/ssz_snappy"
OTHER = "/eth2/b5303f2a/voluntary_exit/ssz_snappy"
NOW = 100_000

# Twelve-second slots and 32 slots per epoch: D = 8, D_low = 6, D_high = 12, D_lazy = 6.
# The fanout lifetime is 60 s, and the seen lifetime 768 s.
PARAMS = parameters(12000, 32)
CHOICES = ClientChoices(
    d_score=4,
    d_out=2,
    gossip_factor=(1, 4),
    gossip_round_up=True,
    flood_publish=False,
    prune_backoff_s=60,
    unsubscribe_backoff_s=10,
)
FLOOD = replace(CHOICES, flood_publish=True)
PEERS = tuple(f"peer-{i:02}".encode() for i in range(40))

M = Message(data=b"block", topic=TOPIC)
M_ID = gossip.message_id(FORK, TOPIC.encode(), M.data)


def _on(topic: str, peers: tuple[bytes, ...]) -> tuple[tuple[bytes, tuple[str, ...]], ...]:
    return tuple((peer, (topic,)) for peer in peers)


def _beat(
    state: RouterState,
    *,
    now: int = NOW,
    choices: ClientChoices = CHOICES,
    ranking: tuple[bytes, ...] = (),
    standing: dict[bytes, Standing] | None = None,
) -> tuple[RouterState, Out]:
    return heartbeat(
        params=PARAMS,
        choices=choices,
        ranking=ranking,
        standing={} if standing is None else standing,
        now_ms=now,
        state=state,
    )


def _join(
    state: RouterState, *, standing: dict[bytes, Standing] | None = None
) -> tuple[RouterState, Out]:
    return join(
        params=PARAMS,
        standing={} if standing is None else standing,
        now_ms=NOW,
        topic=TOPIC,
        state=state,
    )


def _publish(
    state: RouterState,
    *,
    now: int = NOW,
    choices: ClientChoices = CHOICES,
    standing: dict[bytes, Standing] | None = None,
) -> tuple[RouterState, Out]:
    return publish(
        fork=FORK,
        params=PARAMS,
        choices=choices,
        standing={} if standing is None else standing,
        now_ms=now,
        message=M,
        state=state,
    )


def _graft(topic: str) -> Control:
    return Control(graft=(Graft(topic_id=topic),))


def _prune(topic: str, backoff: int) -> Control:
    return Control(prune=(Prune(topic_id=topic, backoff=backoff),))


def _ihave(topic: str, ids: tuple[bytes, ...]) -> Control:
    return Control(ihave=(IHave(topic_id=topic, message_ids=ids),))


# The heartbeat: mesh maintenance.


def test_example_grafts_then_gossips_outside_the_new_mesh() -> None:
    # Steps 1 and 4 of the example of issue 2156.
    # 5 < D_low, so 8 - 5 = 3 peers are grafted.
    # Then 17 candidates remain outside the mesh, and ceil(17 / 4) = 5 < D_lazy, so 6 get IHAVE.
    state = RouterState(
        topics=(TOPIC,),
        peer_topics=_on(TOPIC, PEERS[:25]),
        mesh=((TOPIC, PEERS[:5]),),
        mcache=(((M_ID, M),),),
    )
    new, out = _beat(state)
    assert dict(new.mesh)[TOPIC] == PEERS[:8]
    assert out.control == tuple((peer, _graft(TOPIC)) for peer in PEERS[5:8]) + tuple(
        (peer, _ihave(TOPIC, (M_ID,))) for peer in PEERS[8:14]
    )
    assert new.mcache == ((), ((M_ID, M),))


def test_graft_skips_explicit_negative_and_backed_off_peers() -> None:
    # A backoff that ends now is over; one that ends later is not.
    state = RouterState(
        topics=(TOPIC,),
        peer_topics=_on(TOPIC, PEERS[:12]),
        mesh=((TOPIC, PEERS[:5]),),
        explicit=(PEERS[5],),
        backoff=(((TOPIC, PEERS[6]), NOW + 1), ((TOPIC, PEERS[8]), NOW)),
    )
    new, out = _beat(state, standing={PEERS[7]: Standing(negative=True)})
    assert dict(new.mesh)[TOPIC] == PEERS[:5] + PEERS[8:11]
    assert out.control == tuple((peer, _graft(TOPIC)) for peer in PEERS[8:11])
    assert new.backoff == state.backoff


def test_negative_peer_is_pruned_with_the_backoff() -> None:
    # Step 2 of the example: 13 peers, one negative, leave 12, which is not above D_high.
    state = RouterState(
        topics=(OTHER,), peer_topics=_on(OTHER, PEERS[:13]), mesh=((OTHER, PEERS[:13]),)
    )
    new, out = _beat(state, standing={PEERS[0]: Standing(negative=True)})
    assert dict(new.mesh)[OTHER] == PEERS[1:13]
    assert out.control == ((PEERS[0], _prune(OTHER, 60)),)
    assert new.backoff == (((OTHER, PEERS[0]), NOW + 60_000),)


def test_pruning_never_shortens_a_backoff() -> None:
    state = RouterState(
        topics=(OTHER,),
        peer_topics=_on(OTHER, PEERS[:13]),
        mesh=((OTHER, PEERS[:13]),),
        backoff=(((OTHER, PEERS[0]), NOW + 999_999),),
    )
    new, _ = _beat(state, standing={PEERS[0]: Standing(negative=True)})
    assert new.backoff == (((OTHER, PEERS[0]), NOW + 999_999),)


def test_oversubscribed_mesh_keeps_the_best_then_others_in_mesh_order() -> None:
    # Step 3 of the example: 14 > D_high peers.
    # The 4 best by rank stay, then the first 4 others in mesh order; the 6 left get a PRUNE.
    mesh = PEERS[:14]
    state = RouterState(topics=(OTHER,), peer_topics=_on(OTHER, mesh), mesh=((OTHER, mesh),))
    new, out = _beat(state, ranking=tuple(reversed(mesh)))
    assert dict(new.mesh)[OTHER] == PEERS[13:9:-1] + PEERS[:4]
    assert out.control == tuple((peer, _prune(OTHER, 60)) for peer in PEERS[4:10])
    assert set(new.backoff) == {((OTHER, peer), NOW + 60_000) for peer in PEERS[4:10]}


def test_score_count_decides_how_many_best_peers_stay() -> None:
    mesh = PEERS[:14]
    state = RouterState(topics=(OTHER,), peer_topics=_on(OTHER, mesh), mesh=((OTHER, mesh),))
    ranking = tuple(reversed(mesh))
    none, _ = _beat(state, ranking=ranking, choices=replace(CHOICES, d_score=0))
    assert dict(none.mesh)[OTHER] == PEERS[:8]
    six, _ = _beat(state, ranking=ranking, choices=replace(CHOICES, d_score=6))
    assert dict(six.mesh)[OTHER] == PEERS[13:7:-1] + PEERS[:2]


def test_peer_missing_from_the_ranking_ranks_last() -> None:
    mesh = PEERS[:14]
    state = RouterState(topics=(OTHER,), peer_topics=_on(OTHER, mesh), mesh=((OTHER, mesh),))
    new, _ = _beat(state, ranking=(PEERS[13], PEERS[12]))
    assert dict(new.mesh)[OTHER] == (PEERS[13], PEERS[12]) + PEERS[:6]


def test_oversubscribed_mesh_keeps_the_outbound_quota() -> None:
    # The kept 8 hold no outbound peer, so the last 2 that are not outbound make way.
    # The 2 best-ranked outbound peers left out take their place.
    mesh = PEERS[:14]
    state = RouterState(
        topics=(OTHER,),
        peer_topics=_on(OTHER, mesh),
        mesh=((OTHER, mesh),),
        outbound=PEERS[10:14],
    )
    new, _ = _beat(state, ranking=mesh)
    assert dict(new.mesh)[OTHER] == PEERS[:6] + PEERS[10:12]


def test_outbound_swap_counts_the_outbound_peers_already_kept() -> None:
    mesh = PEERS[:14]
    state = RouterState(
        topics=(OTHER,),
        peer_topics=_on(OTHER, mesh),
        mesh=((OTHER, mesh),),
        outbound=(PEERS[7], *PEERS[10:14]),
    )
    new, _ = _beat(state, ranking=mesh)
    assert dict(new.mesh)[OTHER] == (*PEERS[:6], PEERS[7], PEERS[10])


def test_mesh_with_too_few_outbound_peers_grafts_outbound_ones() -> None:
    # 7 >= D_low peers with no outbound one: 2 outbound peers join, past the target of 8.
    state = RouterState(
        topics=(TOPIC,),
        peer_topics=_on(TOPIC, PEERS[:20]),
        mesh=((TOPIC, PEERS[:7]),),
        outbound=PEERS[15:20],
    )
    new, out = _beat(state)
    assert dict(new.mesh)[TOPIC] == PEERS[:7] + PEERS[15:17]
    assert out.control == tuple((peer, _graft(TOPIC)) for peer in PEERS[15:17])


def test_mesh_of_a_topic_not_joined_is_dropped_without_prune() -> None:
    state = RouterState(peer_topics=_on(TOPIC, PEERS[:3]), mesh=((TOPIC, PEERS[:3]),))
    assert _beat(state) == (replace(state, mesh=(), mcache=((), ())), Out())


# The heartbeat: gossip.


def test_gossip_share_grows_with_the_peers() -> None:
    state = RouterState(
        topics=(TOPIC,),
        peer_topics=_on(TOPIC, PEERS),
        mesh=((TOPIC, PEERS[:8]),),
        mcache=(((M_ID, M),),),
    )
    # 32 candidates: a quarter of them is 8.
    assert len(_beat(state)[1].control) == 8
    # 31 candidates: a quarter is 7.75, so 8 rounded up and 7 rounded down.
    fewer = replace(state, peer_topics=_on(TOPIC, PEERS[:39]))
    assert len(_beat(fewer)[1].control) == 8
    down = replace(CHOICES, gossip_round_up=False)
    assert len(_beat(fewer, choices=down)[1].control) == 7


def test_gossip_skips_peers_below_the_gossip_threshold() -> None:
    state = RouterState(
        topics=(TOPIC,),
        peer_topics=_on(TOPIC, PEERS[:25]),
        mesh=((TOPIC, PEERS[:8]),),
        mcache=(((M_ID, M),),),
    )
    _, out = _beat(state, standing={PEERS[8]: Standing(below_gossip=True)})
    assert out.control == tuple((peer, _ihave(TOPIC, (M_ID,))) for peer in PEERS[9:15])


def test_gossip_for_a_fanout_topic_names_the_gossip_windows_only() -> None:
    old = Message(data=b"old", topic=TOPIC)
    late = Message(data=b"late", topic=TOPIC)
    other = Message(data=b"exit", topic=OTHER)
    old_id = gossip.message_id(FORK, TOPIC.encode(), old.data)
    late_id = gossip.message_id(FORK, TOPIC.encode(), late.data)
    other_id = gossip.message_id(FORK, OTHER.encode(), other.data)
    state = RouterState(
        peer_topics=_on(TOPIC, PEERS[:12]),
        fanout=((TOPIC, PEERS[:8]),),
        last_publish=((TOPIC, NOW),),
        explicit=(PEERS[8],),
        mcache=(((M_ID, M), (other_id, other)), (), ((old_id, old),), ((late_id, late),)),
    )
    _, out = _beat(state)
    # The newest 3 windows, of this topic only, to peers outside the fanout and not explicit.
    assert out.control == tuple((peer, _ihave(TOPIC, (M_ID, old_id))) for peer in PEERS[9:12])


# The heartbeat: fanout and caches.


def test_fanout_expires_after_its_lifetime() -> None:
    state = RouterState(
        peer_topics=_on(TOPIC, PEERS[:8]),
        fanout=((TOPIC, PEERS[:8]),),
        last_publish=((TOPIC, NOW),),
    )
    # The topic stays at exactly 60 s, and leaves 1 ms later.
    assert _beat(state, now=NOW + 60_000)[0].fanout == ((TOPIC, PEERS[:8]),)
    new, _ = _beat(state, now=NOW + 60_001)
    assert new.fanout == ()
    assert new.last_publish == ()


def test_fanout_drops_peers_below_publish_threshold_and_tops_up() -> None:
    state = RouterState(
        peer_topics=_on(TOPIC, PEERS[:12]),
        fanout=((TOPIC, PEERS[:8]),),
        last_publish=((TOPIC, NOW),),
        explicit=(PEERS[8],),
    )
    new, _ = _beat(state, standing={PEERS[0]: Standing(below_publish=True)})
    assert new.fanout == ((TOPIC, (*PEERS[1:8], PEERS[9])),)


def test_heartbeat_drops_expired_seen_entries() -> None:
    state = RouterState(seen=((M_ID, 0),))
    assert _beat(state, now=767_999)[0].seen == ((M_ID, 0),)
    assert _beat(state, now=768_000)[0].seen == ()


# Topic membership.


def test_join_takes_the_fanout_first() -> None:
    state = RouterState(
        peer_topics=_on(TOPIC, PEERS[:12]),
        fanout=((TOPIC, PEERS[10:12]),),
        last_publish=((TOPIC, NOW),),
    )
    new, out = _join(state)
    mesh = PEERS[10:12] + PEERS[:6]
    expected = replace(state, topics=(TOPIC,), mesh=((TOPIC, mesh),), fanout=(), last_publish=())
    assert new == expected
    assert out == Out(control=tuple((peer, _graft(TOPIC)) for peer in mesh))


def test_join_does_not_graft_a_fanout_peer_twice() -> None:
    state = RouterState(
        peer_topics=_on(TOPIC, PEERS[:12]),
        fanout=((TOPIC, PEERS[:2]),),
        last_publish=((TOPIC, NOW),),
    )
    new, out = _join(state)
    assert dict(new.mesh)[TOPIC] == PEERS[:8]
    assert out.control == tuple((peer, _graft(TOPIC)) for peer in PEERS[:8])


def test_join_skips_explicit_negative_and_backed_off_peers() -> None:
    state = RouterState(
        peer_topics=_on(TOPIC, PEERS[:12]),
        fanout=((TOPIC, PEERS[:2]),),
        last_publish=((TOPIC, NOW),),
        explicit=(PEERS[0], PEERS[3]),
        backoff=(((TOPIC, PEERS[1]), NOW + 1), ((TOPIC, PEERS[4]), NOW)),
    )
    new, _ = _join(state, standing={PEERS[5]: Standing(negative=True)})
    assert dict(new.mesh)[TOPIC] == (PEERS[2], PEERS[4], *PEERS[6:12])


def test_join_of_a_joined_topic_changes_nothing() -> None:
    state = RouterState(topics=(TOPIC,), peer_topics=_on(TOPIC, PEERS[:12]))
    assert _join(state) == (state, Out())


def test_leave_prunes_the_mesh_with_the_unsubscribe_backoff() -> None:
    state = RouterState(topics=(TOPIC, OTHER), mesh=((TOPIC, PEERS[:2]), (OTHER, PEERS[2:4])))
    new, out = leave(params=PARAMS, choices=CHOICES, now_ms=NOW, topic=TOPIC, state=state)
    assert new.topics == (OTHER,)
    assert new.mesh == ((OTHER, PEERS[2:4]),)
    assert set(new.backoff) == {((TOPIC, peer), NOW + 10_000) for peer in PEERS[:2]}
    assert out == Out(control=tuple((peer, _prune(TOPIC, 10)) for peer in PEERS[:2]))


def test_leave_of_a_topic_not_joined_changes_nothing() -> None:
    state = RouterState(topics=(OTHER,), mesh=((OTHER, PEERS[:2]),))
    result = leave(params=PARAMS, choices=CHOICES, now_ms=NOW, topic=TOPIC, state=state)
    assert result == (state, Out())


# Publishing.


def test_publish_on_a_joined_topic_goes_to_the_mesh_and_explicit_peers() -> None:
    state = RouterState(
        topics=(TOPIC,),
        peer_topics=_on(TOPIC, PEERS[:4]),
        mesh=((TOPIC, PEERS[:3]),),
        explicit=(PEERS[30],),
    )
    new, out = _publish(state, standing={PEERS[2]: Standing(below_publish=True)})
    assert out == Out(forward=((PEERS[0], M), (PEERS[1], M), (PEERS[30], M)))
    assert new.seen == ((M_ID, NOW),)
    assert new.mcache == (((M_ID, M),),)


def test_publish_off_a_joined_topic_fills_an_empty_fanout() -> None:
    state = RouterState(peer_topics=_on(TOPIC, PEERS[:12]), explicit=(PEERS[0],))
    new, out = _publish(state, standing={PEERS[1]: Standing(below_publish=True)})
    assert new.fanout == ((TOPIC, PEERS[2:10]),)
    assert new.last_publish == ((TOPIC, NOW),)
    assert out == Out(forward=(*((peer, M) for peer in PEERS[2:10]), (PEERS[0], M)))


def test_publish_uses_the_fanout_and_refreshes_its_time() -> None:
    state = RouterState(
        peer_topics=_on(TOPIC, PEERS[:12]),
        fanout=((TOPIC, PEERS[3:6]),),
        last_publish=((TOPIC, 1),),
    )
    new, out = _publish(state, standing={PEERS[4]: Standing(below_publish=True)})
    assert out == Out(forward=((PEERS[3], M), (PEERS[5], M)))
    assert new.fanout == ((TOPIC, PEERS[3:6]),)
    assert new.last_publish == ((TOPIC, NOW),)


def test_flood_publish_reaches_the_mesh_then_the_other_peers() -> None:
    state = RouterState(
        topics=(TOPIC,),
        peer_topics=_on(TOPIC, PEERS[:6]),
        mesh=((TOPIC, (PEERS[4], PEERS[2])),),
        explicit=(PEERS[0], PEERS[30]),
    )
    _, out = _publish(state, choices=FLOOD, standing={PEERS[1]: Standing(below_publish=True)})
    order = (PEERS[4], PEERS[2], PEERS[3], PEERS[5], PEERS[0], PEERS[30])
    assert out == Out(forward=tuple((peer, M) for peer in order))


def test_flood_publish_off_a_joined_topic_keeps_no_fanout() -> None:
    state = RouterState(peer_topics=_on(TOPIC, PEERS[:3]))
    new, out = _publish(state, choices=FLOOD)
    assert (new.fanout, new.last_publish) == ((), ())
    assert out == Out(forward=tuple((peer, M) for peer in PEERS[:3]))


def test_publish_of_a_seen_message_sends_nothing_until_it_expires() -> None:
    state = RouterState(topics=(TOPIC,), mesh=((TOPIC, PEERS[:2]),), seen=((M_ID, 0),))
    assert _publish(state, now=767_999) == (state, Out())
    _, out = _publish(state, now=768_000)
    assert out == Out(forward=((PEERS[0], M), (PEERS[1], M)))


def test_own_message_received_back_is_not_forwarded() -> None:
    state = RouterState(
        topics=(TOPIC,), peer_topics=_on(TOPIC, PEERS[:3]), mesh=((TOPIC, PEERS[:3]),)
    )
    published, _ = _publish(state)
    _, out = receive_rpc(
        fork=FORK,
        params=PARAMS,
        backoff_ms=30_000,
        prune_backoff_ms=60_000,
        standing={},
        validation={M_ID: "accept"},
        now_ms=NOW + 1,
        src=PEERS[0],
        rpc=Rpc(publish=(M,)),
        state=published,
    )
    assert out == Out()


# Client choices outside the bounds of gossipsub v1.1.


@pytest.mark.parametrize(
    "choices",
    [
        replace(CHOICES, d_out=6),
        replace(CHOICES, d_out=5),
        replace(CHOICES, gossip_factor=(1, 0)),
        replace(CHOICES, gossip_factor=(5, 4)),
        replace(CHOICES, prune_backoff_s=0),
        replace(CHOICES, unsubscribe_backoff_s=0),
    ],
)
def test_invalid_client_choices_are_rejected(choices: ClientChoices) -> None:
    message = "client choices outside the bounds of gossipsub v1.1"
    with raises(GossipError, message):
        _beat(RouterState(), choices=choices)
    with raises(GossipError, message):
        _publish(RouterState(), choices=choices)
    with raises(GossipError, message):
        leave(params=PARAMS, choices=choices, now_ms=NOW, topic=TOPIC, state=RouterState())
