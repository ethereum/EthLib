"""multistream-select negotiations and the TCP upgrade, with the examples of their sources."""

import itertools

import pytest

from ethlib.networking.libp2p import multistream, upgrade
from raising import raises

HEADER = b"/multistream/1.0.0"
KAD = b"/ipfs/kad/1.0.0"
KAD_OLD = b"/ipfs/kad/0.2.3"
NOISE = b"/noise"
TLS = b"/tls/1.0.0"
YAMUX = b"/yamux/1.0.0"
MPLEX = b"/mplex/6.7.0"


def frames(*messages: bytes) -> bytes:
    """Messages framed by hand: a one-byte length that counts the newline, the bytes, a newline."""
    assert all(len(message) < 127 for message in messages)
    return b"".join(bytes([len(message) + 1]) + message + b"\n" for message in messages)


# Examples from multiformats/multistream-select, README.md, "Implementation Recommendations".
# Commit 9a1fbe8edadebea223f47102f1913b8026c23a1c.
def test_listener_agrees_in_the_readme_example() -> None:
    received = frames(HEADER, KAD)
    assert multistream.listen((KAD,), received) == ("agreed", KAD, frames(HEADER, KAD), b"")


def test_dialer_agrees_in_the_readme_example() -> None:
    received = frames(HEADER, KAD)
    assert multistream.dial([KAD], received) == ("agreed", KAD, frames(HEADER, KAD), b"")


def test_listener_with_missing_version_support() -> None:
    received = frames(HEADER, KAD, KAD_OLD)
    sent = frames(HEADER, b"na", KAD_OLD)
    assert multistream.listen([KAD_OLD], received) == ("agreed", KAD_OLD, sent, b"")


def test_dialer_with_missing_version_support() -> None:
    received = frames(HEADER, b"na", KAD_OLD)
    sent = frames(HEADER, KAD, KAD_OLD)
    assert multistream.dial([KAD, KAD_OLD], received) == ("agreed", KAD_OLD, sent, b"")


def test_traffic_after_agreement_is_left_unread() -> None:
    # In "Protocol", the traffic of the agreed protocol follows the selection.
    received = frames(HEADER, KAD) + b"<kad-dht-traffic>"
    assert multistream.listen([KAD], received)[3] == b"<kad-dht-traffic>"
    assert multistream.dial([KAD], received)[3] == b"<kad-dht-traffic>"


# libp2p/specs, connections/README.md, "Upgrading Connections".
# Commit c750236de43cd8b246a824b377dfdb26bae686db.
# The listener refuses TLS, then accepts Noise.
def test_connection_upgrade_example() -> None:
    listener = multistream.listen([NOISE], frames(HEADER, TLS, NOISE))
    assert listener == ("agreed", NOISE, frames(HEADER, b"na", NOISE), b"")
    dialer = multistream.dial([TLS, NOISE], listener[2])
    assert dialer == ("agreed", NOISE, frames(HEADER, TLS, NOISE), b"")


def test_listener_answers_ls_with_na() -> None:
    # Listing is optional, and EthLib leaves it out.
    received = frames(HEADER, b"ls")
    assert multistream.listen([KAD], received) == (
        "await_proposal",
        b"",
        frames(HEADER, b"na"),
        b"",
    )


def test_listener_waits_for_more_bytes() -> None:
    assert multistream.listen([KAD], b"") == ("await_header", b"", frames(HEADER), b"")
    assert multistream.listen([KAD], frames(HEADER)) == ("await_proposal", b"", frames(HEADER), b"")


def test_dialer_waits_for_more_bytes() -> None:
    assert multistream.dial([KAD], b"") == ("await_header", b"", frames(HEADER, KAD), b"")
    assert multistream.dial([KAD], frames(HEADER)) == (
        "await_answer",
        b"",
        frames(HEADER, KAD),
        b"",
    )


def test_a_first_message_other_than_the_header_aborts() -> None:
    received = frames(KAD, HEADER)
    assert multistream.listen([KAD], received) == ("aborted", b"", frames(HEADER), frames(HEADER))
    assert multistream.dial([KAD], received) == (
        "aborted",
        b"",
        frames(HEADER, KAD),
        frames(HEADER),
    )


def test_dialer_fails_when_no_proposal_is_left() -> None:
    received = frames(HEADER, b"na")
    assert multistream.dial([KAD], received) == ("failed", b"", frames(HEADER, KAD), b"")


def test_dialer_without_proposals_sends_nothing() -> None:
    assert multistream.dial([], frames(HEADER)) == ("failed", b"", b"", frames(HEADER))


def test_dialer_stops_on_an_unexpected_answer() -> None:
    # The sources fix no reaction to an answer that is neither the proposal nor `na`.
    received = frames(HEADER, MPLEX + b"x")
    sent = frames(HEADER, MPLEX)
    assert multistream.dial([MPLEX], received) == ("unexpected", MPLEX + b"x", sent, b"")


PREFIX = "message {} rejected: EthLib.Networking.Libp2p.Multistream.MultistreamError."


def test_listener_rejects_a_message_that_does_not_decode() -> None:
    with raises(multistream.MultistreamError, PREFIX.format(1) + "empty") as info:
        multistream.listen([KAD], frames(HEADER) + b"\x00")
    assert info.value.code == 2


def test_dialer_rejects_a_message_that_does_not_decode() -> None:
    with raises(multistream.MultistreamError, PREFIX.format(0) + "missingNewline") as info:
        multistream.dial([KAD], bytes.fromhex("036e6161"))
    assert info.value.code == 4


def converse(proposals: list[bytes], supported: list[bytes]) -> tuple[str, bytes, str, bytes]:
    """Feed each peer what the other sent until neither sends more; return both outcomes."""
    to_dialer = b""
    # Each round adds at least one message, and the peers send at most this many in all.
    for _ in range(2 * len(proposals) + 3):
        dialer = multistream.dial(proposals, to_dialer)
        listener = multistream.listen(supported, dialer[2])
        if listener[2] == to_dialer:
            return dialer[0], dialer[1], listener[0], listener[1]
        to_dialer = listener[2]
    pytest.fail("the negotiation did not settle")


PROTOCOLS = [KAD, KAD_OLD, NOISE]
LISTS = [list(p) for n in range(4) for p in itertools.permutations(PROTOCOLS, n)]


@pytest.mark.parametrize(("proposals", "supported"), list(itertools.product(LISTS, LISTS)))
def test_peers_agree_on_the_first_supported_proposal(
    proposals: list[bytes], supported: list[bytes]
) -> None:
    first = next((p for p in proposals if p in supported), None)
    if first is not None:
        assert converse(proposals, supported) == ("agreed", first, "agreed", first)
    elif proposals:
        assert converse(proposals, supported) == ("failed", b"", "await_proposal", b"")
    else:
        assert converse(proposals, supported) == ("failed", b"", "await_header", b"")


def test_a_proposal_named_na_leaves_the_listener_waiting() -> None:
    # The dialer cannot tell an echo of `na` from a refusal, so only it agrees.
    assert converse([b"na"], [KAD]) == ("agreed", b"na", "await_proposal", b"")


# Over TCP, consensus nodes use Noise, require mplex, and put yamux first when they support it.
@pytest.mark.parametrize(
    ("dialer_yamux", "listener_yamux", "muxer"),
    [(True, True, YAMUX), (True, False, MPLEX), (False, True, MPLEX), (False, False, MPLEX)],
)
def test_tcp_upgrade(dialer_yamux: bool, listener_yamux: bool, muxer: bytes) -> None:
    assert upgrade.tcp(dialer_yamux, listener_yamux) == (NOISE, muxer)
