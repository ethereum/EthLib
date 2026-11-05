"""The packets of discv4 against the discovery packets of EIP-8."""

import pytest

from ethlib.cryptography import keccak
from ethlib.cryptography.secp256k1 import recover, sign
from ethlib.networking import discv4, enr

# Section: "Test Vectors", "RLPx Discovery Protocol", of EIP-8.
# Repository: ethereum/EIPs.
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445.
# Licence: CC0-1.0.
# Each packet is signed with KEY, and each one has list items or bytes after its fields.
KEY = bytes.fromhex("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")

PING = bytes.fromhex(
    "e9614ccfd9fc3e74360018522d30e1419a143407ffcce748de3e22116b7e8dc92ff74788c0b6663a"
    "aa3d67d641936511c8f8d6ad8698b820a7cf9e1be7155e9a241f556658c55428ec0563514365799a"
    "4be2be5a685a80971ddcfa80cb422cdd0101ec04cb847f000001820cfa8215a8d790000000000000"
    "000000000000000000018208ae820d058443b9a3550102"
)
PING_555 = bytes.fromhex(
    "577be4349c4dd26768081f58de4c6f375a7a22f3f7adda654d1428637412c3d7fe917cadc56d4e5e"
    "7ffae1dbe3efffb9849feb71b262de37977e7c7a44e677295680e9e38ab26bee2fcbae207fba3ff3"
    "d74069a50b902a82c9903ed37cc993c50001f83e82022bd79020010db83c4d001500000000abcdef"
    "12820cfa8215a8d79020010db885a308d313198a2e037073488208ae82823a8443b9a355c5010203"
    "040531b9019afde696e582a78fa8d95ea13ce3297d4afb8ba6433e4154caa5ac6431af1b80ba7602"
    "3fa4090c408f6b4bc3701562c031041d4702971d102c9ab7fa5eed4cd6bab8f7af956f7d565ee191"
    "7084a95398b6a21eac920fe3dd1345ec0a7ef39367ee69ddf092cbfe5b93e5e568ebc491983c09c7"
    "6d922dc3"
)
PONG = bytes.fromhex(
    "09b2428d83348d27cdf7064ad9024f526cebc19e4958f0fdad87c15eb598dd61d08423e0bf66b206"
    "9869e1724125f820d851c136684082774f870e614d95a2855d000f05d1648b2d5945470bc187c2d2"
    "216fbe870f43ed0909009882e176a46b0102f846d79020010db885a308d313198a2e037073488208"
    "ae82823aa0fbc914b16819237dcd8801d7e53f69e9719adecb3cc0e790c57e91ca4461c9548443b9"
    "a355c6010203c2040506a0c969a58f6f9095004c0177a6b47f451530cab38966a25cca5cb58f0555"
    "42124e"
)
FIND_NODE = bytes.fromhex(
    "c7c44041b9f7c7e41934417ebac9a8e1a4c6298f74553f2fcfdcae6ed6fe53163eb3d2b52e39fe91"
    "831b8a927bf4fc222c3902202027e5e9eb812195f95d20061ef5cd31d502e47ecb61183f74a504fe"
    "04c51e73df81f25c4d506b26db4517490103f84eb840ca634cae0d49acb401d8a4c6b6fe8c55b70d"
    "115bf400769cc1400f3258cd31387574077f301b421bc84df7266c44e9e6d569fc56be0081290476"
    "7bf5ccd1fc7f8443b9a35582999983999999280dc62cc8255c73471e0a61da0c89acdc0e035e260a"
    "dd7fc0c04ad9ebf3919644c91cb247affc82b69bd2ca235c71eab8e49737c937a2c396"
)
NEIGHBORS = bytes.fromhex(
    "c679fc8fe0b8b12f06577f2e802d34f6fa257e6137a995f6f4cbfc9ee50ed3710faf6e66f932c4c8"
    "d81d64343f429651328758b47d3dbc02c4042f0fff6946a50f4a49037a72bb550f3a7872363a83e1"
    "b9ee6469856c24eb4ef80b7535bcf99c0004f9015bf90150f84d846321163782115c82115db84031"
    "55e1427f85f10a5c9a7755877748041af1bcd8d474ec065eb33df57a97babf54bfd2103575fa8291"
    "15d224c523596b401065a97f74010610fce76382c0bf32f84984010203040101b840312c55512422"
    "cf9b8a4097e9a6ad79402e87a15ae909a4bfefa22398f03d20951933beea1e4dfa6f968212385e82"
    "9f04c2d314fc2d4e255e0d3bc08792b069dbf8599020010db83c4d001500000000abcdef12820d05"
    "820d05b84038643200b172dcfef857492156971f0e6aa2c538d8b74010f8e140811d53b98c765dd2"
    "d96126051913f44582e8c199ad7c6d6819e9a56483f637feaac9448aacf8599020010db885a308d3"
    "13198a2e037073488203e78203e8b8408dcab8618c3253b558d459da53bd8fa68935a719aff8b811"
    "197101a4b2b47dd2d47295286fc00cc081bb542d760717d1bdd6bec2c37cd72eca367d6dd3b9df73"
    "8443b9a355010203b525a138aa34383fec3d2719a0"
)

# Section: "Test Vectors" of EIP-778, a record signed with the same key.
# Repository: ethereum/EIPs.
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445.
# Licence: CC0-1.0.
RECORD_TEXT = (
    "enr:-IS4QHCYrYZbAKWCBRlAy5zzaDZXJBGkcnh4MHcBFZntXNFrdvJjX04jRzjzCBOonrkTfj499SZuOh8R33Ls8RRc"
    "y5wBgmlkgnY0gmlwhH8AAAGJc2VjcDI1NmsxoQPKY0yuDUmstAHYpMa2_oxVtw0RW_QAdpzBQA8yWM0xOIN1ZHCCdl8"
)


def public_key(key: bytes) -> bytes:
    """The 64 bytes `x || y` of the public key of `key`, recovered from one of its signatures."""
    signature = sign(key, bytes(32))
    point = recover(bytes(32), signature[:64], signature[64])
    assert len(point) == 65 and point[0] == 0x04
    return point[1:]


def _split(data: bytes) -> tuple[int, int]:
    """The sizes of the prefix and of the payload of the RLP item at the start of `data`."""
    first = data[0]
    if first < 0x80:
        return 0, 1
    short = first - (0xC0 if first >= 0xC0 else 0x80)
    if short < 56:
        return 1, short
    length_size = short - 55
    return 1 + length_size, int.from_bytes(data[1 : 1 + length_size], "big")


def _raw_items(data: bytes) -> list[bytes]:
    """The encodings of the items of the RLP list at the start of `data`."""
    prefix, length = _split(data)
    payload, items = data[prefix : prefix + length], []
    while payload:
        size = sum(_split(payload))
        items.append(payload[:size])
        payload = payload[size:]
    return items


def _rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(items)
    if len(payload) < 56:
        return bytes([0xC0 + len(payload)]) + payload
    length = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([0xF7 + len(length)]) + length + payload


def _kept(packet: bytes, count: int) -> bytes:
    """The content `packet-type || packet-data` with only the first `count` items of the data."""
    return packet[97:98] + _rlp_list(_raw_items(packet[98:])[:count])


@pytest.mark.parametrize(
    ("packet", "count"),
    [
        # Ping keeps its four fields and the sequence number of EIP-868, the item 01.
        (PING, 5),
        (FIND_NODE, 2),
        (NEIGHBORS, 2),
    ],
)
def test_eip8_packets(packet: bytes, count: int) -> None:
    out = discv4.decode(packet)
    assert out[:32] == packet[:32]
    assert out[32:96] == public_key(KEY)
    assert out[96:] == _kept(packet, count)


@pytest.mark.parametrize("packet", [PING_555, PONG])
def test_eip8_packets_older_than_eip868(packet: bytes) -> None:
    # The item after the fixed fields is a list, where EIP-868 puts the sequence number.
    _, *rest = _raw_items(packet[98:])
    assert any(item[0] >= 0xC0 for item in rest)
    with pytest.raises(discv4.Discv4Error) as info:
        discv4.decode(packet)
    assert info.value.code == 7


@pytest.mark.parametrize("packet", [PING, FIND_NODE, NEIGHBORS])
def test_round_trip(packet: bytes) -> None:
    content = _kept(packet, 5 if packet is PING else 2)
    encoded = discv4.encode(KEY, content)
    assert encoded[:32] == keccak.keccak256(encoded[32:])
    assert discv4.decode(encoded) == encoded[:32] + public_key(KEY) + content


def test_ping_without_sequence_number() -> None:
    content = _kept(PING, 4)
    encoded = discv4.encode(KEY, content)
    assert discv4.decode(encoded)[96:] == content


@pytest.mark.parametrize("position", [0, 31, 32, 96, 97, len(PING) - 1])
def test_changed_byte_fails(position: int) -> None:
    # The hash covers every byte after it, so any change breaks it.
    changed = bytearray(PING)
    changed[position] ^= 0x01
    with pytest.raises(discv4.Discv4Error) as info:
        discv4.decode(bytes(changed))
    assert info.value.code == 3


def test_size_bounds() -> None:
    with pytest.raises(discv4.Discv4Error) as info:
        discv4.decode(PING + bytes(1281 - len(PING)))
    assert info.value.code == 1
    with pytest.raises(discv4.Discv4Error) as info:
        discv4.decode(PING[:97])
    assert info.value.code == 2


def test_unknown_type() -> None:
    signed = b"\x07\xc0"
    body = sign(KEY, keccak.keccak256(signed)) + signed
    with pytest.raises(discv4.Discv4Error) as info:
        discv4.decode(keccak.keccak256(body) + body)
    assert info.value.code == 6
    with pytest.raises(discv4.Discv4Error) as info:
        discv4.encode(KEY, signed)
    assert info.value.code == 6


def test_enr_response() -> None:
    record = enr.from_text(RECORD_TEXT)
    request = discv4.encode(KEY, b"\x05" + _rlp_list([b"\x84\x43\xb9\xa3\x55"]))
    # The response echoes the hash of the request, then holds the record.
    response = discv4.encode(KEY, b"\x06" + _rlp_list([b"\xa0" + request[:32], record]))
    out = discv4.decode(response)
    assert out[96:] == b"\x06" + _rlp_list([b"\xa0" + request[:32], record])
    assert discv4.record_signed_by(b"\x04" + public_key(KEY), record)
    other = bytes(31) + b"\x01"
    assert not discv4.record_signed_by(b"\x04" + public_key(other), record)
