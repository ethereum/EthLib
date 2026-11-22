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
from ethlib.serialization import rlp
from raising import raises

# A private key of secp256k1: the scalar 1.
SECRET = bytes(31) + b"\x01"

# The compressed generator of secp256k1, a valid public key.
GENERATOR = bytes.fromhex("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")

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
        # A record of a signature and a sequence number has no id.
        pytest.param(
            EnrError,
            13,
            "record has no id",
            lambda: enr.node_id(rlp.encode([bytes(64), b"\x01"])),
            id="enr-node-id",
        ),
        # A private key is 32 bytes.
        pytest.param(
            EnrError,
            0,
            "private key is not 32 bytes below the group order",
            lambda: enr.sign_v4(b"", enr.make_record_v4(SECRET, 1, rlp.encode([]))),
            id="enr-sign-key",
        ),
        # Two bytes that are not one RLP item.
        pytest.param(
            EnrError,
            2,
            "record is not one RLP item",
            lambda: enr.sign_v4(SECRET, b"\x01\x02"),
            id="enr-sign-record",
        ),
        # Two bytes that are not one RLP item.
        pytest.param(
            EnrError,
            2,
            "record is not one RLP item",
            lambda: enr.make_record_v4(SECRET, 1, b"\x01\x02"),
            id="enr-make-rlp",
        ),
        # The pairs are an RLP list, not an empty string.
        pytest.param(
            EnrError,
            3,
            "record is not an RLP list",
            lambda: enr.make_record_v4(SECRET, 1, rlp.encode(b"")),
            id="enr-make-list",
        ),
        # The key id comes without its value.
        pytest.param(
            EnrError,
            8,
            "the last key has no value",
            lambda: enr.make_record_v4(SECRET, 1, rlp.encode([b"id"])),
            id="enr-make-pairs",
        ),
        # A record with no other pair has no eth2 entry.
        pytest.param(
            EnrError,
            101,
            "record has no eth2 entry",
            lambda: enr.consensus_entries("fusaka", enr.make_record_v4(SECRET, 1, rlp.encode([]))),
            id="enr-entries",
        ),
        # The eth entry is a byte string, not a list.
        pytest.param(
            EnrError,
            0,
            "eth entry is not a list that starts with [forkHash, forkNext]",
            lambda: enr.eth_fork_id(enr.make_record_v4(SECRET, 1, rlp.encode([b"eth", b"\x01"]))),
            id="enr-eth",
        ),
        # An IPv4 address is 4 bytes, not 1.
        pytest.param(
            EnrError,
            17,
            "the 0x6970 entry is not an address of its size",
            lambda: enr.endpoints(enr.make_record_v4(SECRET, 1, rlp.encode([b"ip", b"\x01"]))),
            id="enr-endpoints",
        ),
        # Two bytes that are not one RLP item.
        pytest.param(
            EnrError,
            2,
            "record is not one RLP item",
            lambda: enr.verify_v4(b"\x01\x02"),
            id="enr-verify",
        ),
        # A branch is not a root.
        pytest.param(
            DnsDiscError,
            2,
            "root does not have the fields e=, l=, seq= and sig=, in that order",
            lambda: dnsdisc.verify_root(bytes(33), "enrtree-branch:"),
            id="dnsdisc-verify-root",
        ),
        # The text nope has no known prefix.
        pytest.param(
            DnsDiscError,
            1,
            "text is not a root, a branch, a link or a node record",
            lambda: dnsdisc.verify_root(bytes(33), "nope"),
            id="dnsdisc-verify-parse",
        ),
        # The empty table has no TXT record at the domain.
        pytest.param(
            DnsDiscError,
            10,
            "no TXT record at x",
            lambda: dnsdisc.resolve(bytes(33), 0, "x", 10, {}),
            id="dnsdisc-resolve",
        ),
        # A private key is 32 bytes.
        pytest.param(
            DnsDiscError,
            0,
            "private key is not 32 bytes below the group order",
            lambda: dnsdisc.sign_root(b"", bytes(16), bytes(16), 0),
            id="dnsdisc-sign-key",
        ),
        # The content has at least its type byte.
        pytest.param(
            Discv4Error,
            0,
            "content is empty",
            lambda: discv4.encode(SECRET, b""),
            id="discv4-encode-empty",
        ),
        # 0x81 starts a string that the input ends inside.
        pytest.param(
            Discv4Error,
            0,
            "packet data is not one RLP item",
            lambda: discv4.encode(SECRET, b"\x01\x81"),
            id="discv4-encode-rlp",
        ),
        # The packet data is a list, not an empty string.
        pytest.param(
            Discv4Error,
            0,
            "packet data is not an RLP list",
            lambda: discv4.encode(SECRET, b"\x01\x80"),
            id="discv4-encode-bytes",
        ),
        # A Ping has more fields than the empty list.
        pytest.param(
            Discv4Error,
            7,
            "packet data is not RLP of the expected shape",
            lambda: discv4.encode(SECRET, b"\x01\xc0"),
            id="discv4-encode-packet",
        ),
        # A private key is 32 bytes.
        pytest.param(
            Discv4Error,
            0,
            "bad private key size: 0, expected 32",
            lambda: discv4.encode(b"", b"\x01\xc0"),
            id="discv4-encode-key",
        ),
        # A public key is 33 or 65 bytes.
        pytest.param(
            Discv4Error,
            0,
            "bad point encoding size: 0, expected 33 or 65",
            lambda: discv4.record_signed_by(b"", b""),
            id="discv4-signed-key",
        ),
        # Two bytes that are not one RLP item.
        pytest.param(
            Discv4Error,
            0,
            "record is not one RLP item",
            lambda: discv4.record_signed_by(GENERATOR, b"\x01\x02"),
            id="discv4-signed-record",
        ),
        # The empty input is too short for a header and a packet type.
        pytest.param(
            Discv4Error,
            2,
            "packet has 0 bytes, too few for a header and a packet type",
            lambda: discv4.accept_enr_response(b"", b""),
            id="discv4-accept",
        ),
        # Message ID 4 is past the p2p messages.
        pytest.param(
            Devp2pError,
            4,
            "message ID 4 is not a p2p message",
            lambda: devp2p.encode_message(False, b"\x04\xc0"),
            id="devp2p-encode",
        ),
        # The empty input is not one RLP item.
        pytest.param(
            ForkIdError,
            0,
            "schedule is not one RLP item",
            lambda: forkid.fork_id(b"", 0, 0),
            id="forkid-schedule-rlp",
        ),
        # A schedule has four items, not none.
        pytest.param(
            ForkIdError,
            0,
            "schedule is not [genesis-hash, genesis-time, merge-fork, forks]",
            lambda: forkid.fork_id(rlp.encode([]), 0, 0),
            id="forkid-schedule-shape",
        ),
        # The remote announces a fork hash that the chain never had.
        pytest.param(
            ForkIdError,
            2,
            "chains are incompatible, or the local node is stale",
            lambda: forkid.validate(
                forkid.schedule(bytes(32), 0, []), 0, 0, forkid.encode(b"\xff" * 4, 0)
            ),
            id="forkid-refused",
        ),
        # The empty chunk has no response code.
        pytest.param(
            ReqRespError,
            7,
            "response chunk has no response code",
            lambda: reqresp.decode_response_chunk(0, 0, 10, b""),
            id="reqresp-chunk",
        ),
        # A public key is 33 or 65 bytes.
        pytest.param(
            RlpxError,
            0,
            "bad point encoding size: 0, expected 33 or 65",
            lambda: rlpx.ecies_encrypt(b"", SECRET, bytes(16), b"", b""),
            id="rlpx-public-key",
        ),
        # An IV is 16 bytes.
        pytest.param(
            RlpxError,
            0,
            "bad iv size: 15, expected 16",
            lambda: rlpx.make_auth(SECRET, SECRET, bytes(32), GENERATOR, SECRET, bytes(15), b""),
            id="rlpx-iv",
        ),
        # A nonce is 32 bytes.
        pytest.param(
            RlpxError,
            0,
            "bad nonce size: 31, expected 32",
            lambda: rlpx.finish(SECRET, SECRET, bytes(31), b"", b"", b""),
            id="rlpx-nonce",
        ),
        # The empty ack has no size prefix.
        pytest.param(
            RlpxError,
            102,
            "packet of 0 bytes does not match its size prefix",
            lambda: rlpx.finish(SECRET, SECRET, bytes(32), b"", b"", b""),
            id="rlpx-handshake",
        ),
        # The empty auth has no size prefix.
        pytest.param(
            RlpxError,
            102,
            "packet of 0 bytes does not match its size prefix",
            lambda: rlpx.recipient_secrets(SECRET, SECRET, bytes(32), b"", b"", b""),
            id="rlpx-recipient",
        ),
        # Two bytes that are not one RLP item.
        pytest.param(
            RlpxError,
            0,
            "frames is not an RLP list of byte strings",
            lambda: rlpx.write_frames(bytes(32), bytes(32), bytes(32), b"\x01\x02"),
            id="rlpx-frames-rlp",
        ),
        # Ten bytes are too few for a packet.
        pytest.param(
            Discv5Error,
            1,
            "invalid packet: EthLib.Networking.Discv5.PacketError.size 10",
            lambda: discv5.read_whoareyou(bytes(32), bytes(10)),
            id="discv5-session-packet",
        ),
        # A WHOAREYOU packet is not an ordinary message packet.
        pytest.param(
            Discv5Error,
            204,
            "packet has flag 1, not 0",
            lambda: discv5.open_message(
                bytes(16),
                bytes(32),
                bytes(32),
                discv5.make_whoareyou(bytes(32), bytes(16), bytes(12), bytes(16), 0)[0],
            ),
            id="discv5-session-flag",
        ),
        # Ten bytes are too few for a packet.
        pytest.param(
            Discv5Error,
            1,
            "invalid packet: EthLib.Networking.Discv5.PacketError.size 10",
            lambda: discv5.open_handshake(SECRET, b"", bytes(32), GENERATOR, bytes(10)),
            id="discv5-handshake-packet",
        ),
        # A WHOAREYOU packet is not a handshake packet.
        pytest.param(
            Discv5Error,
            310,
            "packet has flag 1, not 2",
            lambda: discv5.open_handshake(
                SECRET,
                b"",
                bytes(32),
                GENERATOR,
                discv5.make_whoareyou(bytes(32), bytes(16), bytes(12), bytes(16), 0)[0],
            ),
            id="discv5-handshake-flag",
        ),
        # The empty input is no point of secp256k1.
        pytest.param(
            Discv5Error,
            0,
            "public key is not a point of secp256k1",
            lambda: discv5.ecdh(SECRET, b""),
            id="discv5-public-key",
        ),
        # A session key is 16 bytes.
        pytest.param(
            Discv5Error,
            0,
            "key is not 16 bytes",
            lambda: discv5.encrypt_message(bytes(15), bytes(12), b"", b""),
            id="discv5-key",
        ),
        # A nonce is 12 bytes.
        pytest.param(
            Discv5Error,
            0,
            "nonce is not 12 bytes",
            lambda: discv5.encrypt_message(bytes(16), bytes(11), b"", b""),
            id="discv5-nonce",
        ),
        # A tag of zeros does not authenticate.
        pytest.param(
            Discv5Error,
            0,
            "message does not authenticate",
            lambda: discv5.decrypt_message(bytes(16), bytes(12), bytes(16), b""),
            id="discv5-decrypt",
        ),
        # A masking IV is 16 bytes.
        pytest.param(
            Discv5Error,
            0,
            "masking IV has 15 bytes, not 16",
            lambda: discv5.make_whoareyou(bytes(32), bytes(15), bytes(12), bytes(16), 0),
            id="discv5-masking-iv",
        ),
        # A PING is not a TALKREQ.
        pytest.param(
            Discv5Error,
            0,
            "message is not a TALKREQ",
            lambda: discv5.talk_response(b"\x01\xc2\x01\x01"),
            id="discv5-talk",
        ),
        # A message has at least its type byte.
        pytest.param(
            Discv5Error,
            101,
            "invalid message: empty",
            lambda: discv5.talk_response(b""),
            id="discv5-talk-message",
        ),
        # A message has at least its type byte.
        pytest.param(
            Discv5Error,
            101,
            "invalid message: empty",
            lambda: discv5.answers_request(b"", b""),
            id="discv5-answers",
        ),
        # A message has at least its type byte.
        pytest.param(
            Discv5Error,
            101,
            "invalid message: empty",
            lambda: discv5.reencode_message(b""),
            id="discv5-reencode",
        ),
        # Ten bytes are too few for a packet.
        pytest.param(
            Discv5Error,
            1,
            "invalid packet: EthLib.Networking.Discv5.PacketError.size 10",
            lambda: discv5.reencode_packet(bytes(32), bytes(10)),
            id="discv5-reencode-packet",
        ),
        # Two bytes that are not one RLP item.
        pytest.param(
            Discv5Error,
            0,
            "record is not one RLP item",
            lambda: discv5.nodes_match(bytes(32), [], [b"\x01\x02"]),
            id="discv5-nodes-match",
        ),
        # The empty input is no point of secp256k1.
        pytest.param(
            Discv5Error,
            0,
            "public key is not a point of secp256k1",
            lambda: discv5.derive_keys(SECRET, b"", bytes(32), bytes(32), b""),
            id="discv5-derive-keys",
        ),
        # A private key is 32 bytes.
        pytest.param(
            Discv5Error,
            0,
            "private key is not 32 bytes below the group order",
            lambda: discv5.id_sign(b"", b"", b"", bytes(32)),
            id="discv5-id-sign",
        ),
        # A message of length zero.
        pytest.param(
            MultistreamError,
            2,
            "message 0 rejected: EthLib.Networking.Libp2p.Multistream.MultistreamError.empty",
            lambda: multistream.listen([b"/x"], b"\x00"),
            id="multistream-listen",
        ),
        # A message of length zero.
        pytest.param(
            MultistreamError,
            2,
            "message 0 rejected: EthLib.Networking.Libp2p.Multistream.MultistreamError.empty",
            lambda: multistream.dial([b"/x"], b"\x00"),
            id="multistream-dial",
        ),
        # Flag 7 is not an mplex flag.
        pytest.param(
            MplexError,
            2,
            "event 0: mplex frame rejected: EthLib.Networking.Libp2p.Mplex.MplexError.unknownFlag",
            lambda: mplex.session([(True, b"\x07\x00")]),
            id="mplex-session-frame",
        ),
        # A message on stream 1, which no frame opened.
        pytest.param(
            MplexError,
            102,
            "event 0: stream 1 (opened locally: false) is unknown",
            lambda: mplex.session([(True, b"\x0a\x00")]),
            id="mplex-session-step",
        ),
        # A stream ID is below 2^60.
        pytest.param(
            MplexError,
            0,
            (
                "frame must have a stream ID below 2^60, at most 1 MiB of data, "
                "and no data on a close or a reset"
            ),
            lambda: mplex.encode(mplex.Frame(stream_id=2**60, flag=mplex.Flag.NEW_STREAM)),
            id="mplex-encode",
        ),
        # Version 1, where yamux defines only version 0.
        pytest.param(
            YamuxError,
            2,
            "event 0: yamux frame rejected: EthLib.Networking.Libp2p.Yamux.YamuxError.version 1",
            lambda: yamux.session(False, [(True, b"\x01" + bytes(11))]),
            id="yamux-session-frame",
        ),
        # A data frame on stream 1, which no frame opened.
        pytest.param(
            YamuxError,
            104,
            "event 0: stream 1 is unknown",
            lambda: yamux.session(False, [(True, bytes(7) + b"\x01" + bytes(4))]),
            id="yamux-session-step",
        ),
        # A data frame of length 1 carries one byte, not none.
        pytest.param(
            YamuxError,
            0,
            "frame must carry as many bytes as its length for data, else none",
            lambda: yamux.encode(yamux.Frame(kind=yamux.Kind.DATA, flags=0, stream_id=1, length=1)),
            id="yamux-encode",
        ),
        # A chain holds exactly one certificate, not none.
        pytest.param(
            TlsCertificateError,
            4,
            "TLS certificate rejected: EthLib.Networking.Libp2p.Tls.TlsCertError.chain 0",
            lambda: tls.authenticate(
                {"host_algorithms": [], "certificate_algorithms": [], "reject_unique_ids": False},
                0,
                [],
            ),
            id="tls-authenticate",
        ),
        # A chain holds exactly one certificate, not none.
        pytest.param(
            TlsCertificateError,
            4,
            "TLS certificate rejected: EthLib.Networking.Libp2p.Tls.TlsCertError.chain 0",
            lambda: tls.authenticate_peer(
                {"host_algorithms": [], "certificate_algorithms": [], "reject_unique_ids": False},
                0,
                b"",
                [],
            ),
            id="tls-authenticate-peer",
        ),
        # The empty input has no first byte.
        pytest.param(
            QuicError,
            1,
            "QUIC header rejected: EthLib.Networking.Quic.Wire.Error.truncated 1 0",
            lambda: quic.decode_header(0, b""),
            id="quic-header-decode",
        ),
        # A truncated packet number of one byte is below 2^8.
        pytest.param(
            QuicError,
            7,
            (
                "QUIC packet number rejected: "
                "EthLib.Networking.Quic.Wire.Error.packetNumber 4611686018427387904 1 0"
            ),
            lambda: quic.decode_packet_number(0, 2**62, 0),
            id="quic-number-decode",
        ),
        # The empty input has no 2-byte length.
        pytest.param(
            NoiseError,
            3,
            "EthLib.Networking.Noise.NoiseError.truncated 2 0",
            lambda: noise.unframe(b""),
            id="noise-unframe",
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
