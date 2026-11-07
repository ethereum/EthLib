"""Ethereum Node Records against the test vector of EIP-778."""

from ethlib.networking import enr
from raising import raises

# The record, its RLP structure and its node ID come from "Test Vectors" in EIP-778.
#
# File: EIPS/eip-778.md
# Repository: ethereum/EIPs
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445
# Licence: CC0-1.0

TEXT = (
    "enr:-IS4QHCYrYZbAKWCBRlAy5zzaDZXJBGkcnh4MHcBFZntXNFrdvJjX04jRzjzCBOonrkTfj499SZuOh8R33Ls8RRc"
    "y5wBgmlkgnY0gmlwhH8AAAGJc2VjcDI1NmsxoQPKY0yuDUmstAHYpMa2_oxVtw0RW_QAdpzBQA8yWM0xOIN1ZHCCdl8"
)
NODE_ID = bytes.fromhex("a448f24c6d18e575453db13171562b71999873db5b286df957af199ec94617f7")
SIGNATURE = bytes.fromhex(
    "7098ad865b00a582051940cb9cf36836572411a47278783077011599ed5cd16b"
    "76f2635f4e234738f30813a89eb9137e3e3df5266e3a1f11df72ecf1145ccb9c"
)
PUBLIC_KEY = bytes.fromhex("03ca634cae0d49acb401d8a4c6b6fe8c55b70d115bf400769cc1400f3258cd3138")


def _rlp_bytes(data: bytes) -> bytes:
    # Every byte string here is under 256 bytes, so a long length takes one byte.
    if len(data) == 1 and data[0] < 0x80:
        return data
    if len(data) < 56:
        return bytes([0x80 + len(data)]) + data
    assert len(data) < 256
    return bytes([0xB8, len(data)]) + data


def _rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(_rlp_bytes(item) for item in items)
    # The record lists here are between 56 and 255 bytes long.
    assert 56 <= len(payload) < 256
    return bytes([0xF8, len(payload)]) + payload


PAIRS = [
    (b"id", b"v4"),
    (b"ip", bytes.fromhex("7f000001")),
    (b"secp256k1", PUBLIC_KEY),
    (b"udp", bytes.fromhex("765f")),
]


def _record(pairs) -> bytes:
    return _rlp_list([SIGNATURE, b"\x01"] + [x for pair in pairs for x in pair])


def test_eip_vector() -> None:
    record = enr.from_text(TEXT)
    assert record == _record(PAIRS)
    assert enr.seq(record) == 1
    assert enr.verify_v4(record)
    assert enr.node_id(record) == NODE_ID


def test_changed_signature_fails() -> None:
    bad = SIGNATURE[:-1] + bytes([SIGNATURE[-1] ^ 1])
    record = _rlp_list([bad, b"\x01"] + [x for pair in PAIRS for x in pair])
    assert not enr.verify_v4(record)


def test_unsorted_keys_rejected() -> None:
    with raises(ValueError, "the keys are not sorted"):
        enr.seq(_record([PAIRS[1], PAIRS[0], PAIRS[2], PAIRS[3]]))


def test_repeated_key_rejected() -> None:
    with raises(ValueError, "a key is repeated"):
        enr.seq(_record([PAIRS[0], PAIRS[1], PAIRS[1], PAIRS[2], PAIRS[3]]))


def test_missing_id_rejected() -> None:
    # The key `id` is the one key that every record must have.
    with raises(ValueError, "record has no id"):
        enr.seq(_record(PAIRS[1:]))


def test_too_large_rejected() -> None:
    record = _record(PAIRS)
    with raises(ValueError, "record has 301 bytes, more than 300"):
        enr.seq(record + b"\x00" * (enr.MAX_RECORD_SIZE + 1 - len(record)))


def test_text_without_prefix_rejected() -> None:
    with raises(ValueError, "text does not start with enr:"):
        enr.from_text(TEXT[len("enr:") :])


def test_nonzero_pad_bits_rejected() -> None:
    # The last character goes from 8 to 9, which sets a bit past the end of the bytes.
    assert TEXT.endswith("8")
    with raises(ValueError, "text is not unpadded URL-safe base64"):
        enr.from_text(TEXT[:-1] + "9")


def test_padded_text_rejected() -> None:
    with raises(ValueError, "text is not unpadded URL-safe base64"):
        enr.from_text(TEXT + "=")


# The private key of the record of "Test Vectors" in EIP-778.
SECRET_KEY = bytes.fromhex("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")


def test_sign_v4_eip_vector() -> None:
    # Signing the record again with its private key gives the record of the EIP, byte for byte.
    record = enr.from_text(TEXT)
    assert enr.sign_v4(SECRET_KEY, record) == record


def test_sign_v4_replaces_the_signature() -> None:
    # A record with any other signature comes back with the signature of the EIP.
    record = _rlp_list([bytes(64), b"\x01"] + [x for pair in PAIRS for x in pair])
    signed = enr.sign_v4(SECRET_KEY, record)
    assert signed == enr.from_text(TEXT)
    assert enr.verify_v4(signed)


def test_sign_v4_with_another_key_does_not_verify() -> None:
    # The signature of another key does not verify under the secp256k1 pair of the record.
    other = (1).to_bytes(32, "big")
    assert not enr.verify_v4(enr.sign_v4(other, enr.from_text(TEXT)))


def test_sign_v4_rejects_a_zero_key() -> None:
    with raises(ValueError, "the record could not be signed"):
        enr.sign_v4(bytes(32), enr.from_text(TEXT))


# The order of the group of secp256k1.
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def test_sign_v4_rejects_a_short_key() -> None:
    with raises(ValueError, "private key is not 32 bytes below the group order"):
        enr.sign_v4(SECRET_KEY[1:], enr.from_text(TEXT))


def test_sign_v4_rejects_the_group_order() -> None:
    with raises(ValueError, "private key is not 32 bytes below the group order"):
        enr.sign_v4(ORDER.to_bytes(32, "big"), enr.from_text(TEXT))


def _pairs_list(pairs) -> bytes:
    # The other pairs of the EIP record, ip and udp, as one short RLP list.
    payload = b"".join(_rlp_bytes(x) for pair in pairs for x in pair)
    assert len(payload) < 56
    return bytes([0xC0 + len(payload)]) + payload


def test_make_record_v4_eip_vector() -> None:
    # The builder adds id and secp256k1 to ip and udp, and signs, giving the EIP's record.
    pairs = _pairs_list([PAIRS[1], PAIRS[3]])
    assert enr.make_record_v4(SECRET_KEY, 1, pairs) == enr.from_text(TEXT)


def test_make_record_v4_rejects_its_own_keys() -> None:
    # The pair id is the builder's own, so a second one repeats the key.
    with raises(ValueError, "a key is repeated"):
        enr.make_record_v4(SECRET_KEY, 1, _pairs_list([PAIRS[0], PAIRS[1], PAIRS[3]]))


def test_make_record_v4_rejects_unsorted_pairs() -> None:
    with raises(ValueError, "the keys are not sorted"):
        enr.make_record_v4(SECRET_KEY, 1, _pairs_list([PAIRS[3], PAIRS[1]]))


def test_make_record_v4_rejects_a_short_key() -> None:
    with raises(ValueError, "private key is not 32 bytes below the group order"):
        enr.make_record_v4(SECRET_KEY[1:], 1, _pairs_list([PAIRS[1], PAIRS[3]]))


def test_make_record_v4_rejects_the_group_order() -> None:
    with raises(ValueError, "private key is not 32 bytes below the group order"):
        enr.make_record_v4(ORDER.to_bytes(32, "big"), 1, _pairs_list([PAIRS[1], PAIRS[3]]))
