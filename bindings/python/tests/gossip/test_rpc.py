"""Gossipsub RPC frames built by hand from the libp2p protobuf schemas."""

from collections.abc import Callable

import pytest
from hypothesis import given, strategies as st

from ethlib.networking.gossip import rpc
from raising import raises

# The schemas are in libp2p/specs at commit c750236de43cd8b246a824b377dfdb26bae686db.
# RPC and Message are in pubsub/README.md, sections "The RPC" and "The Message".
# The control messages are in "Protobuf" of pubsub/gossipsub/gossipsub-v1.0.md and v1.1.md.
# The IDONTWANT message is in "Protobuf Extension" of pubsub/gossipsub/gossipsub-v1.2.md.
# The encoding guide is content/programming-guides/encoding.md of protocolbuffers.github.io.
# That repository is pinned at commit bc2f346991e20631ed0a884e345110738228bfae.
# Its section "Message Structure" makes a key the varint of 8 * field number + wire type.
# Wire type 0 is a varint, 1 eight bytes, 2 a length and bytes, 3 and 4 a group, 5 four bytes.

PREFIX = "gossip RPC rejected: EthLib.Networking.Gossip.RpcError."
PROTOBUF = PREFIX + "protobuf (EthLib.Networking.Encoding.Protobuf.ProtobufError."


def _varint(n: int) -> bytes:
    """The unsigned varint of a number: seven bits per byte, low bits first."""
    out = bytearray()
    while True:
        low = n & 0x7F
        n >>= 7
        out.append(low | (0x80 if n else 0))
        if not n:
            return bytes(out)


def _uint(field: int, n: int) -> bytes:
    """A varint record."""
    return _varint(field << 3) + _varint(n)


def _len(field: int, payload: bytes) -> bytes:
    """A length-delimited record."""
    return _varint(field << 3 | 2) + _varint(len(payload)) + payload


def _str(field: int, text: str) -> bytes:
    """A string record, in UTF-8."""
    return _len(field, text.encode())


def _message(*records: bytes) -> bytes:
    """An RPC that publishes one message made of the records."""
    return _len(2, b"".join(records))


def _control(*records: bytes) -> bytes:
    """An RPC with one control record made of the records."""
    return _len(3, b"".join(records))


# One RPC with every field, each written in the order and form of the encoder of EthLib.
# Every singular field is written, even at its default, so the bytes are also its encoding.
# Each top-level list, control list and inner list of a first entry has two distinct entries.
# So a reversed or shuffled list shows.
FULL_BYTES = b"".join(
    [
        _len(1, _uint(1, 1) + _str(2, "a")),
        _len(1, _uint(1, 0) + _str(2, "")),
        _message(_len(2, b"\x01\x02"), _str(4, "t")),
        _message(_len(2, b""), _str(4, "u")),
        _control(
            _len(1, _str(1, "t") + _len(2, b"m1") + _len(2, b"m2")),
            _len(1, _str(1, "u")),
            _len(2, _len(1, b"m3") + _len(1, b"m5")),
            _len(2, _len(1, b"m6")),
            _len(3, _str(1, "g")),
            _len(3, _str(1, "h")),
            _len(
                4,
                _str(1, "p")
                + _len(2, _len(1, b"id") + _len(2, b"rec"))
                + _len(2, _len(1, b"id2") + _len(2, b""))
                + _uint(3, 60),
            ),
            _len(4, _str(1, "q") + _uint(3, 2**64 - 1)),
            _len(5, _len(1, b"m4") + _len(1, b"m7")),
            _len(5, _len(1, b"m8")),
        ),
    ]
)
FULL = rpc.Rpc(
    subscriptions=(rpc.SubOpts(subscribe=True, topic_id="a"), rpc.SubOpts()),
    publish=(rpc.Message(data=b"\x01\x02", topic="t"), rpc.Message(topic="u")),
    control=rpc.Control(
        ihave=(rpc.IHave(topic_id="t", message_ids=(b"m1", b"m2")), rpc.IHave(topic_id="u")),
        iwant=(rpc.IWant(message_ids=(b"m3", b"m5")), rpc.IWant(message_ids=(b"m6",))),
        graft=(rpc.Graft(topic_id="g"), rpc.Graft(topic_id="h")),
        prune=(
            rpc.Prune(
                topic_id="p",
                peers=(
                    rpc.PeerInfo(peer_id=b"id", signed_peer_record=b"rec"),
                    rpc.PeerInfo(peer_id=b"id2"),
                ),
                backoff=60,
            ),
            rpc.Prune(topic_id="q", backoff=2**64 - 1),
        ),
        idontwant=(rpc.IDontWant(message_ids=(b"m4", b"m7")), rpc.IDontWant(message_ids=(b"m8",))),
    ),
)


def _reference(value: rpc.Rpc) -> bytes:
    """The bytes of an RPC, written field by field from the schemas, in the order of FULL_BYTES."""
    control = value.control
    records = [
        *(_len(1, _uint(1, int(s.subscribe)) + _str(2, s.topic_id)) for s in value.subscriptions),
        *(_message(_len(2, m.data), _str(4, m.topic)) for m in value.publish),
    ]
    inner = [
        *(
            _len(1, _str(1, m.topic_id) + b"".join(_len(2, i) for i in m.message_ids))
            for m in control.ihave
        ),
        *(_len(2, b"".join(_len(1, i) for i in m.message_ids)) for m in control.iwant),
        *(_len(3, _str(1, m.topic_id)) for m in control.graft),
        *(
            _len(
                4,
                _str(1, m.topic_id)
                + b"".join(
                    _len(2, _len(1, p.peer_id) + _len(2, p.signed_peer_record)) for p in m.peers
                )
                + _uint(3, m.backoff),
            )
            for m in control.prune
        ),
        *(_len(5, b"".join(_len(1, i) for i in m.message_ids)) for m in control.idontwant),
    ]
    if inner:
        records.append(_control(*inner))
    return b"".join(records)


def test_reference_writes_full() -> None:
    assert _reference(FULL) == FULL_BYTES


def test_decode_every_field() -> None:
    assert rpc.decode(FULL_BYTES) == FULL


def test_encode_every_field() -> None:
    assert rpc.encode(FULL) == FULL_BYTES


def test_empty_rpc() -> None:
    assert rpc.decode(b"") == rpc.Rpc()
    assert rpc.encode(rpc.Rpc()) == b""


def test_encode_omits_an_empty_control() -> None:
    assert rpc.encode(rpc.Rpc(control=rpc.Control())) == b""


@pytest.mark.parametrize(
    ("data", "expected"),
    [
        # An empty subscription: not subscribed, empty topic ID.
        (_len(1, b""), rpc.Rpc(subscriptions=(rpc.SubOpts(),))),
        # A message with a topic and no data.
        (_message(_str(4, "t")), rpc.Rpc(publish=(rpc.Message(topic="t"),))),
        # An empty control record, which adds nothing.
        (_control(), rpc.Rpc()),
        # Empty IHAVE, IWANT, GRAFT and IDONTWANT messages.
        (
            _control(_len(1, b""), _len(2, b""), _len(3, b""), _len(5, b"")),
            rpc.Rpc(
                control=rpc.Control(
                    ihave=(rpc.IHave(),),
                    iwant=(rpc.IWant(),),
                    graft=(rpc.Graft(),),
                    idontwant=(rpc.IDontWant(),),
                )
            ),
        ),
        # An empty PRUNE reads with a backoff of 0, and an empty peer with empty fields.
        (_control(_len(4, b"")), rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(),)))),
        (
            _control(_len(4, _len(2, b""))),
            rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(peers=(rpc.PeerInfo(),)),))),
        ),
    ],
)
def test_missing_fields_read_as_defaults(data: bytes, expected: rpc.Rpc) -> None:
    assert rpc.decode(data) == expected


def test_any_nonzero_subscribe_reads_as_true() -> None:
    # A bool is written as 0 or 1; EthLib reads any other value as true.
    assert rpc.decode(_len(1, _uint(1, 2))) == rpc.Rpc(subscriptions=(rpc.SubOpts(subscribe=True),))


@pytest.mark.parametrize("field", [1, 3, 5, 6])
@pytest.mark.parametrize(
    "record",
    [
        pytest.param(lambda field: _len(field, b""), id="empty"),
        pytest.param(lambda field: _len(field, b"\x01"), id="non-empty"),
        pytest.param(lambda field: _uint(field, 0), id="varint"),
    ],
)
def test_strict_no_sign_forbids_a_field(field: int, record: Callable[[int], bytes]) -> None:
    # StrictNoSign forbids from (1), seqno (3), signature (5) and key (6), whatever their form.
    data = _message(_str(4, "t"), record(field))
    with raises(rpc.GossipError, PREFIX + f"signed {field}") as info:
        rpc.decode(data)
    assert info.value.code == 102


def test_the_first_forbidden_field_is_reported() -> None:
    with raises(rpc.GossipError, PREFIX + "signed 5"):
        rpc.decode(_message(_len(5, b""), _str(4, "t"), _len(1, b"")))


@pytest.mark.parametrize(
    "data",
    [
        _message(),
        _message(_len(2, b"\x01")),
        # A string under a field number that the schema does not name is not a topic.
        _message(_len(7, b"t")),
    ],
)
def test_message_without_topic(data: bytes) -> None:
    with raises(rpc.GossipError, PREFIX + "missingTopic") as info:
        rpc.decode(data)
    assert info.value.code == 103


@pytest.mark.parametrize(
    ("data", "field"),
    [
        # The byte ff never occurs in UTF-8, and c3 needs a continuation byte.
        (_message(_len(4, b"\xff")), 4),
        (_message(_len(4, b"ok"), _len(4, b"\xc3")), 4),
        (_len(1, _len(2, b"\xff")), 2),
        (_control(_len(1, _len(1, b"\xff"))), 1),
        (_control(_len(3, _len(1, b"\xff"))), 1),
        (_control(_len(4, _len(1, b"\xff"))), 1),
        # A surrogate half encoded in three bytes is not UTF-8.
        (_message(_len(4, b"\xed\xa0\x80")), 4),
    ],
)
def test_topic_that_is_not_utf8(data: bytes, field: int) -> None:
    with raises(rpc.GossipError, PREFIX + f"utf8 {field}") as info:
        rpc.decode(data)
    assert info.value.code == 105


def test_topic_is_unicode() -> None:
    data = _message(_str(4, "é/中"))
    assert rpc.decode(data) == rpc.Rpc(publish=(rpc.Message(topic="é/中"),))


# One record of each wire type with field number 9, which no schema here names.
# The group holds a field-1 varint, which a skipped group must not expose.
UNKNOWN = (
    _uint(9, 300)
    + _varint(9 << 3 | 1)
    + bytes(8)
    + _len(9, b"xyz")
    + _varint(9 << 3 | 3)
    + _uint(1, 7)
    + _varint(9 << 3 | 4)
    + _varint(9 << 3 | 5)
    + bytes(4)
)


@pytest.mark.parametrize(
    ("data", "expected"),
    [
        (UNKNOWN, rpc.Rpc()),
        (
            _len(1, UNKNOWN + _str(2, "a")),
            rpc.Rpc(subscriptions=(rpc.SubOpts(topic_id="a"),)),
        ),
        (_message(UNKNOWN, _str(4, "t")), rpc.Rpc(publish=(rpc.Message(topic="t"),))),
        (_control(UNKNOWN), rpc.Rpc()),
        (
            _control(_len(1, UNKNOWN), _len(2, UNKNOWN), _len(3, UNKNOWN), _len(5, UNKNOWN)),
            rpc.Rpc(
                control=rpc.Control(
                    ihave=(rpc.IHave(),),
                    iwant=(rpc.IWant(),),
                    graft=(rpc.Graft(),),
                    idontwant=(rpc.IDontWant(),),
                )
            ),
        ),
        (
            _control(_len(4, _len(2, UNKNOWN))),
            rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(peers=(rpc.PeerInfo(),)),))),
        ),
        (
            _control(_len(4, UNKNOWN + _uint(3, 5))),
            rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(backoff=5),))),
        ),
    ],
)
def test_unknown_fields_are_skipped(data: bytes, expected: rpc.Rpc) -> None:
    assert rpc.decode(data) == expected


@pytest.mark.parametrize(
    ("data", "fault"),
    [
        # Subscriptions, published messages and control are length-delimited.
        (_uint(1, 0), "1 0"),
        (_uint(2, 0), "2 0"),
        (_uint(3, 0), "3 0"),
        # The subscribe flag is a varint, the topic ID a string.
        (_len(1, _len(1, b"")), "1 2"),
        (_len(1, _uint(2, 0)), "2 0"),
        # The data and the topic of a message are length-delimited.
        (_message(_uint(2, 0), _str(4, "t")), "2 0"),
        (_message(_uint(4, 0)), "4 0"),
        # A fixed-width record in place of a message ID.
        (_control(_len(2, _varint(1 << 3 | 5) + bytes(4))), "1 5"),
        # The backoff is a varint, and a peer is length-delimited.
        (_control(_len(4, _len(3, b""))), "3 2"),
        (_control(_len(4, _uint(2, 0))), "2 0"),
        # The ID and the signed record of a peer are length-delimited.
        (_control(_len(4, _len(2, _uint(1, 0)))), "1 0"),
        (_control(_len(4, _len(2, _uint(2, 0)))), "2 0"),
        # The topics and message IDs of the control messages are length-delimited.
        (_control(_len(1, _uint(1, 0))), "1 0"),
        (_control(_len(1, _uint(2, 0))), "2 0"),
        (_control(_len(3, _uint(1, 0))), "1 0"),
        (_control(_len(4, _uint(1, 0))), "1 0"),
        (_control(_len(5, _uint(1, 0))), "1 0"),
        # A group in place of an IHAVE.
        (_control(_varint(1 << 3 | 3) + _varint(1 << 3 | 4)), "1 3"),
    ],
)
def test_known_field_with_another_wire_type(data: bytes, fault: str) -> None:
    with raises(rpc.GossipError, PREFIX + "wireType " + fault) as info:
        rpc.decode(data)
    assert info.value.code == 104


@pytest.mark.parametrize(
    ("data", "expected"),
    [
        (
            _len(1, _uint(1, 1) + _str(2, "a") + _uint(1, 0) + _str(2, "b")),
            rpc.Rpc(subscriptions=(rpc.SubOpts(subscribe=False, topic_id="b"),)),
        ),
        (
            _message(_len(2, b"x"), _str(4, "a"), _len(2, b"y"), _str(4, "b")),
            rpc.Rpc(publish=(rpc.Message(data=b"y", topic="b"),)),
        ),
        (
            _control(_len(4, _uint(3, 1) + _str(1, "a") + _uint(3, 2) + _str(1, "b"))),
            rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(topic_id="b", backoff=2),))),
        ),
        (
            _control(_len(4, _len(2, _len(1, b"a") + _len(1, b"b")))),
            rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(peers=(rpc.PeerInfo(peer_id=b"b"),)),))),
        ),
        (
            _control(_len(1, _str(1, "a") + _str(1, "b")), _len(3, _str(1, "c") + _str(1, "d"))),
            rpc.Rpc(
                control=rpc.Control(
                    ihave=(rpc.IHave(topic_id="b"),), graft=(rpc.Graft(topic_id="d"),)
                )
            ),
        ),
    ],
)
def test_last_value_wins(data: bytes, expected: rpc.Rpc) -> None:
    assert rpc.decode(data) == expected


def test_a_forbidden_field_wins_over_other_faults() -> None:
    with raises(rpc.GossipError, PREFIX + "signed 1"):
        rpc.decode(_message(_len(4, b"\xff"), _len(1, b"")))


def test_subscriptions_are_checked_before_control() -> None:
    # The control record comes first in the bytes, but the subscriptions are read first.
    data = _control(_len(3, _len(1, b"\xff"))) + _len(1, _len(2, b"\xff"))
    with raises(rpc.GossipError, PREFIX + "utf8 2"):
        rpc.decode(data)


def test_non_minimal_varints_are_accepted() -> None:
    # The key 8a 00 is field 1 with wire type 2, and the length 80 00 is 0.
    assert rpc.decode(b"\x8a\x00\x80\x00") == rpc.Rpc(subscriptions=(rpc.SubOpts(),))


def test_backoff_of_two_to_the_64_overflows() -> None:
    # The ten bytes 80 .. 80 02 hold 2^64.
    data = _control(_len(4, _varint(3 << 3) + b"\x80" * 9 + b"\x02"))
    message = (
        PREFIX + "protobuf\n  (EthLib.Networking.Encoding.Protobuf.ProtobufError.varint "
        "(EthLib.Networking.Encoding.Varint.VarintError.overflow))"
    )
    with raises(rpc.GossipError, message):
        rpc.decode(data)


def test_earlier_values_must_still_be_well_formed() -> None:
    # The second topic is valid, but the first is still read, and it is not UTF-8.
    with raises(rpc.GossipError, PREFIX + "utf8 4"):
        rpc.decode(_message(_len(4, b"\xff"), _str(4, "t")))


def test_control_records_merge_in_order() -> None:
    data = (
        _control(_len(3, _str(1, "a")), _len(2, _len(1, b"1")))
        + _len(1, _str(2, "s"))
        + _control(_len(3, _str(1, "b")), _len(5, _len(1, b"2")))
    )
    assert rpc.decode(data) == rpc.Rpc(
        subscriptions=(rpc.SubOpts(topic_id="s"),),
        control=rpc.Control(
            iwant=(rpc.IWant(message_ids=(b"1",)),),
            graft=(rpc.Graft(topic_id="a"), rpc.Graft(topic_id="b")),
            idontwant=(rpc.IDontWant(message_ids=(b"2",)),),
        ),
    )


def test_control_split_across_two_records_is_rejected() -> None:
    # Joined, the two payloads would be one GRAFT of topic "a".
    # Each control record is decoded alone, so the first ends inside the GRAFT.
    graft = _len(3, _str(1, "a"))
    data = _control(graft[:2]) + _control(graft[2:])
    with raises(rpc.GossipError, PROTOBUF + "truncated)") as info:
        rpc.decode(data)
    assert info.value.code == 101


@pytest.mark.parametrize(
    ("data", "fault"),
    [
        # A length of 4 with three bytes after it.
        (_varint(2 << 3 | 2) + b"\x04abc", "truncated)"),
        # A truncated record inside a published message.
        (_len(2, _varint(4 << 3 | 2) + b"\x02a"), "truncated)"),
        # A fixed-width record cut short.
        (_varint(9 << 3 | 1) + bytes(7), "truncated)"),
        # A group that never ends.
        (_varint(9 << 3 | 3), "truncated)"),
        # Field number 0, at the top and inside a message.
        (_uint(0, 0), "fieldNumber 0)"),
        (_message(_uint(0, 0)), "fieldNumber 0)"),
        # Wire types 6 and 7 do not exist.
        (_varint(1 << 3 | 6), "wireType 6)"),
        (_varint(1 << 3 | 7), "wireType 7)"),
        # A group end outside any group.
        (_varint(9 << 3 | 4), "wireType 4)"),
        # A group that ends with another field number.
        (_varint(9 << 3 | 3) + _varint(8 << 3 | 4), "groupEnd 8)"),
    ],
)
def test_bytes_that_are_not_protobuf(data: bytes, fault: str) -> None:
    with raises(rpc.GossipError, PROTOBUF + fault) as info:
        rpc.decode(data)
    assert info.value.code == 101


def test_key_cut_inside_its_varint() -> None:
    data = b"\x8a"
    message = (
        PREFIX + "protobuf\n  (EthLib.Networking.Encoding.Protobuf.ProtobufError.varint\n"
        "    (EthLib.Networking.Encoding.Varint.VarintError.unterminated))"
    )
    with raises(rpc.GossipError, message) as info:
        rpc.decode(data)
    assert info.value.code == 101


def test_encode_refuses_a_backoff_of_two_to_the_64() -> None:
    value = rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(backoff=2**64),)))
    message = (
        "control: prune: backoff: expected an int below 18446744073709551616, "
        "got 18446744073709551616"
    )
    with raises(rpc.GossipError, message) as info:
        rpc.encode(value)
    assert info.value.code == 0


def test_encode_refuses_a_topic_that_is_not_unicode_text() -> None:
    # A lone surrogate has no UTF-8 form, so the converter refuses it before the Lean encoder runs.
    value = rpc.Rpc(publish=(rpc.Message(topic="\ud800"),))
    message = "'utf-8' codec can't encode character '\\ud800' in position 0: surrogates not allowed"
    with raises(UnicodeEncodeError, message):
        rpc.encode(value)


def test_encode_refuses_a_negative_backoff_before_lean() -> None:
    # The converter refuses a negative int with a plain ValueError, before the Lean encoder runs.
    value = rpc.Rpc(control=rpc.Control(prune=(rpc.Prune(backoff=-1),)))
    with raises(ValueError, "cannot pass a negative int to Lean"):
        rpc.encode(value)


_ids = st.lists(st.binary(max_size=4), max_size=3).map(tuple)
_topics = st.text(max_size=4)
_peers = st.builds(
    rpc.PeerInfo, peer_id=st.binary(max_size=4), signed_peer_record=st.binary(max_size=4)
)
RPCS = st.builds(
    rpc.Rpc,
    subscriptions=st.lists(
        st.builds(rpc.SubOpts, subscribe=st.booleans(), topic_id=_topics), max_size=2
    ).map(tuple),
    publish=st.lists(
        st.builds(rpc.Message, data=st.binary(max_size=4), topic=_topics), max_size=2
    ).map(tuple),
    control=st.builds(
        rpc.Control,
        ihave=st.lists(st.builds(rpc.IHave, topic_id=_topics, message_ids=_ids), max_size=2).map(
            tuple
        ),
        iwant=st.lists(st.builds(rpc.IWant, message_ids=_ids), max_size=2).map(tuple),
        graft=st.lists(st.builds(rpc.Graft, topic_id=_topics), max_size=2).map(tuple),
        prune=st.lists(
            st.builds(
                rpc.Prune,
                topic_id=_topics,
                peers=st.lists(_peers, max_size=2).map(tuple),
                backoff=st.integers(0, 2**64 - 1),
            ),
            max_size=2,
        ).map(tuple),
        idontwant=st.lists(st.builds(rpc.IDontWant, message_ids=_ids), max_size=2).map(tuple),
    ),
)


@given(RPCS)
def test_encode_matches_the_reference(value: rpc.Rpc) -> None:
    assert rpc.encode(value) == _reference(value)


@given(RPCS)
def test_decode_reads_the_reference(value: rpc.Rpc) -> None:
    assert rpc.decode(_reference(value)) == value
