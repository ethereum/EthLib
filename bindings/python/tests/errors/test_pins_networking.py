"""The code and message of the errors that the networking exports pass to Python."""

from collections.abc import Callable

import pytest

from ethlib.errors import (
    Devp2pError,
    Discv4Error,
    Discv5Error,
    DnsDiscError,
    EnrError,
    EthLibError,
    ForkIdError,
    GossipError,
    Libp2pIdentityError,
    MplexError,
    MultistreamError,
    NoiseError,
    QuicError,
    QuicProtectionError,
    QuicVarintError,
    ReqRespError,
    RlpxError,
    SnappyError,
    Tls13Error,
    TlsCertificateError,
    TlsHandshakeError,
    TlsStepError,
    UvarintError,
    VarintError,
    YamuxError,
)
from ethlib.networking import (
    devp2p,
    discv4,
    discv5,
    dnsdisc,
    enr,
    forkid,
    gossip,
    noise,
    quic,
    reqresp,
    rlpx,
    snappy,
    uvarint,
    varint,
)
from ethlib.networking.gossip import rpc
from ethlib.networking.libp2p import identity, mplex, multistream, tls, yamux
from ethlib.networking.quic import handshake, tls as quic_tls
from raising import raises

# An export turns the typed error of an operation into a code and a message.
# Each case pins one way of doing so, with the code and the message that Python sees.


@pytest.mark.parametrize(
    ("error", "code", "message", "call"),
    [
        # Two bytes that are not one RLP item.
        pytest.param(
            EnrError,
            2,
            "record is not one RLP item",
            lambda: enr.seq(b"\x01\x02"),
            id="enr-record",
        ),
        # The text form of a record starts with enr:.
        pytest.param(
            EnrError,
            11,
            "text does not start with enr:",
            lambda: enr.from_text("nope"),
            id="enr-text",
        ),
        # The initiator writes the first message, so it cannot read one.
        pytest.param(
            NoiseError,
            1,
            "EthLib.Networking.Noise.NoiseError.wrongPhase true 0",
            lambda: noise.read_message(
                noise.initialize(True, bytes(31) + b"\x01", bytes(31) + b"\x02", b""), b""
            ),
            id="noise",
        ),
        # A private key is 32 bytes.
        pytest.param(
            NoiseError,
            0,
            "expected 32 bytes, got 31",
            lambda: noise.initialize(True, bytes(31), bytes(32), b""),
            id="noise-argument",
        ),
        # Ten bytes are too few for a packet.
        pytest.param(
            Discv5Error,
            1,
            "invalid packet: EthLib.Networking.Discv5.PacketError.size 10",
            lambda: discv5.decode_packet(bytes(32), bytes(10)),
            id="discv5-packet",
        ),
        # A message has at least its type byte.
        pytest.param(
            Discv5Error,
            101,
            "invalid message: empty",
            lambda: discv5.decode_message(b""),
            id="discv5-message",
        ),
        # No message has type 11.
        pytest.param(
            Discv5Error,
            102,
            "invalid message: unknown type 11",
            lambda: discv5.decode_message(b"\x0b\xc0"),
            id="discv5-message-type",
        ),
        # A PING whose body is an empty string, not a list.
        pytest.param(
            Discv5Error,
            103,
            "invalid message: not one RLP list, or a field of the wrong form",
            lambda: discv5.decode_message(b"\x01\x80"),
            id="discv5-message-rlp",
        ),
        # A node ID is 32 bytes.
        pytest.param(
            Discv5Error,
            0,
            "node ID has 31 bytes, not 32",
            lambda: discv5.log_distance(bytes(31), bytes(32)),
            id="discv5-argument",
        ),
        # The bound for 2^64 - 1 bytes is 2^64 or more.
        pytest.param(
            ReqRespError,
            3,
            "bound on the compressed size is 2^64 or more",
            lambda: reqresp.max_compressed_len(2**64 - 1),
            id="reqresp",
        ),
        # The empty input has no length prefix.
        pytest.param(
            ReqRespError,
            1,
            (
                "length prefix is not a valid varint: "
                "EthLib.Networking.Encoding.Varint.VarintError.unterminated"
            ),
            lambda: reqresp.decode_payload(0, 10, b""),
            id="reqresp-payload",
        ),
        # An ECIES message has at least 113 bytes.
        pytest.param(
            RlpxError,
            1,
            "ciphertext has 10 bytes, fewer than 113",
            lambda: rlpx.ecies_decrypt(bytes(31) + b"\x01", b"", bytes(10)),
            id="rlpx-ecies",
        ),
        # A frame under zero secrets does not carry the right header MAC.
        pytest.param(
            RlpxError,
            203,
            "header MAC does not match",
            lambda: rlpx.read_frames(bytes(32), bytes(32), bytes(32), bytes(32)),
            id="rlpx-frame",
        ),
        # An AES secret is 32 bytes.
        pytest.param(
            RlpxError,
            0,
            "bad secret size: 31, expected 32",
            lambda: rlpx.write_frames(bytes(31), bytes(32), bytes(32), b"\xc1\x80"),
            id="rlpx-argument",
        ),
        # Message ID 4 is past the p2p messages.
        pytest.param(
            Devp2pError,
            4,
            "message ID 4 is not a p2p message",
            lambda: devp2p.decode_message(False, b"\x04\xc0"),
            id="devp2p",
        ),
        # The empty Hello is not an RLP list.
        pytest.param(
            Devp2pError,
            0,
            "our Hello: message is not RLP of the expected shape",
            lambda: devp2p.session(b"", []),
            id="devp2p-session",
        ),
        # Ten bytes are too few for a header and a packet type.
        pytest.param(
            Discv4Error,
            2,
            "packet has 10 bytes, too few for a header and a packet type",
            lambda: discv4.decode(bytes(10)),
            id="discv4",
        ),
        # The text nope has no known prefix.
        pytest.param(
            DnsDiscError,
            1,
            "text is not a root, a branch, a link or a node record",
            lambda: dnsdisc.parse_entry("nope"),
            id="dnsdisc",
        ),
        # The text nope has no known prefix.
        pytest.param(
            DnsDiscError,
            1,
            "text is not a root, a branch, a link or a node record",
            lambda: dnsdisc.parse_url("nope"),
            id="dnsdisc-url",
        ),
        # Ten zero bytes are not an RLP fork identifier.
        pytest.param(
            ForkIdError,
            0,
            "remote is not an RLP fork identifier",
            lambda: forkid.validate(forkid.schedule(bytes(32), 0, []), 0, 0, bytes(10)),
            id="forkid",
        ),
        # 0xff starts a length that the input ends inside.
        pytest.param(
            SnappyError,
            1,
            "block rejected: EthLib.Networking.Snappy.SnappyError.preambleTruncated",
            lambda: snappy.decompress(b"\xff"),
            id="snappy",
        ),
        # A stream starts with the stream identifier chunk.
        pytest.param(
            SnappyError,
            101,
            (
                "stream rejected: "
                "EthLib.Networking.Snappy.FrameError.missingStreamIdentifier (some 0)"
            ),
            lambda: snappy.decode_frames(b"\x00"),
            id="snappy-frames",
        ),
        # The continuation bit is set on the last byte.
        pytest.param(
            VarintError,
            1,
            "varint rejected: EthLib.Networking.Encoding.Varint.VarintError.unterminated",
            lambda: varint.decode(b"\x80"),
            id="varint",
        ),
        # The continuation bit is set on the last byte.
        pytest.param(
            UvarintError,
            1,
            (
                "unsigned varint rejected: "
                "EthLib.Networking.Encoding.Uvarint.UvarintError.varint "
                "(EthLib.Networking.Encoding.Varint.VarintError.unterminated)"
            ),
            lambda: uvarint.decode(b"\x80"),
            id="uvarint",
        ),
        # A multiformats varint holds values below 2^63.
        pytest.param(
            UvarintError,
            0,
            "value must be below 2^63",
            lambda: uvarint.encode(2**63),
            id="uvarint-encode",
        ),
        # The prefix 01 announces two bytes, and the input has one.
        pytest.param(
            QuicVarintError,
            1,
            "QUIC integer rejected: EthLib.Networking.Quic.Varint.VarintError.truncated 2 1",
            lambda: quic.decode_varint(b"\x40"),
            id="quic-varint",
        ),
        # A QUIC integer is below 2^62.
        pytest.param(
            QuicVarintError,
            0,
            "value must be below 2^62",
            lambda: quic.encode_varint(2**62),
            id="quic-varint-encode",
        ),
        # 0x1f is not a QUIC frame type.
        pytest.param(
            QuicError,
            8,
            "QUIC frame rejected: EthLib.Networking.Quic.Wire.Error.frameEncoding",
            lambda: quic.decode_frame("initial", b"\x1f"),
            id="quic-frame",
        ),
        # A packet number is below 2^62.
        pytest.param(
            QuicError,
            0,
            "expected an int below 4611686018427387904, got 4611686018427387904",
            lambda: quic.packet_number_width(2**62, None),
            id="quic-width",
        ),
        # A two-byte payload leaves no 16-byte sample for header protection.
        pytest.param(
            QuicProtectionError,
            2,
            "EthLib.Networking.Quic.Protection.Error.sample 1 20",
            lambda: quic.protect("TLS_AES_128_GCM_SHA256", bytes(32), 0, 1, b"\x40\x00", bytes(2)),
            id="quic-protection",
        ),
        # No cipher suite has the name nope.
        pytest.param(
            Tls13Error,
            0,
            "expected TLS_AES_128_GCM_SHA256 or TLS_CHACHA20_POLY1305_SHA256, got nope",
            lambda: quic.packet_keys("nope", bytes(32)),  # ty: ignore[invalid-argument-type]
            id="tls13-quic",
        ),
        # One type byte, with no room for the three-byte length.
        pytest.param(
            TlsHandshakeError,
            1,
            "EthLib.Networking.Quic.Tls.Wire.Error.truncated 3 0",
            lambda: quic_tls.decode_message(32, b"\x01"),
            id="tls-handshake",
        ),
        # The configuration names no key policy.
        pytest.param(
            TlsStepError,
            0,
            "no key policy",
            lambda: handshake.client_start({}),  # ty: ignore[invalid-argument-type, missing-typed-dict-key]
            id="tls-step",
        ),
        # A message of length zero.
        pytest.param(
            MultistreamError,
            2,
            (
                "multistream message rejected: "
                "EthLib.Networking.Libp2p.Multistream.MultistreamError.empty"
            ),
            lambda: multistream.decode(b"\x00"),
            id="multistream",
        ),
        # Flag 7 is not an mplex flag.
        pytest.param(
            MplexError,
            2,
            "mplex frame rejected: EthLib.Networking.Libp2p.Mplex.MplexError.unknownFlag",
            lambda: mplex.decode(b"\x07\x00"),
            id="mplex",
        ),
        # Version 1, where yamux defines only version 0.
        pytest.param(
            YamuxError,
            2,
            "yamux frame rejected: EthLib.Networking.Libp2p.Yamux.YamuxError.version 1",
            lambda: yamux.decode(b"\x01" + bytes(11)),
            id="yamux",
        ),
        # The empty input is no DER value.
        pytest.param(
            TlsCertificateError,
            1,
            (
                "TLS certificate rejected: EthLib.Networking.Libp2p.Tls.TlsCertError.der "
                "(EthLib.Serialization.Der.Error.truncated 2 0)"
            ),
            lambda: tls.read_certificate(b""),
            id="tls-certificate",
        ),
        # The secret key 0 is not in [1, n - 1].
        pytest.param(
            Libp2pIdentityError,
            3,
            "libp2p identity rejected: EthLib.Networking.Libp2p.IdentityError.privateKey",
            lambda: identity.public_key(bytes(32)),
            id="libp2p-identity",
        ),
        # A secret key is 32 bytes.
        pytest.param(
            Libp2pIdentityError,
            0,
            "expected 32 bytes, got 31",
            lambda: identity.public_key(bytes(31)),
            id="libp2p-identity-argument",
        ),
        # No fork has the name nofork.
        pytest.param(
            GossipError,
            0,
            "no fork named nofork",
            lambda: gossip.message_id("nofork", b"", b""),
            id="gossip-fork",
        ),
        # 0xff starts a Snappy length that the input ends inside.
        pytest.param(
            GossipError,
            3,
            (
                "gossip payload rejected: EthLib.Networking.Gossip.PayloadError.snappy "
                "(EthLib.Networking.Snappy.SnappyError.preambleTruncated)"
            ),
            lambda: gossip.decode_payload(10, b"\xff"),
            id="gossip-payload",
        ),
        # 0xff starts a protobuf varint that the input ends inside.
        pytest.param(
            GossipError,
            101,
            (
                "gossip RPC rejected: EthLib.Networking.Gossip.RpcError.protobuf\n  "
                "(EthLib.Networking.Encoding.Protobuf.ProtobufError.varint\n    "
                "(EthLib.Networking.Encoding.Varint.VarintError.unterminated))"
            ),
            lambda: rpc.decode(b"\xff"),
            id="gossip-rpc",
        ),
    ],
)
def test_code_and_message(
    error: type[EthLibError], code: int, message: str, call: Callable[[], object]
) -> None:
    with raises(error, message) as info:
        call()
    assert type(info.value) is error
    assert info.value.code == code
