"""Ethereum Node Records against the test vector of EIP-778.

The record, its RLP structure and its node ID come from "Test Vectors" in EIP-778, at
commit d386b29b5a31bd5cfd8d21bbf4e8a0c87734085e of ethereum/EIPs, under CC0-1.0.
"""

import pytest

from ethlib.networking import enr

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
    with pytest.raises(ValueError, match="the keys are not sorted"):
        enr.seq(_record([PAIRS[1], PAIRS[0], PAIRS[2], PAIRS[3]]))


def test_repeated_key_rejected() -> None:
    with pytest.raises(ValueError, match="a key is repeated"):
        enr.seq(_record([PAIRS[0], PAIRS[1], PAIRS[1], PAIRS[2], PAIRS[3]]))


def test_missing_id_rejected() -> None:
    # The key `id` is the one key that every record must have.
    with pytest.raises(ValueError, match="record has no id"):
        enr.seq(_record(PAIRS[1:]))


def test_too_large_rejected() -> None:
    record = _record(PAIRS)
    with pytest.raises(ValueError):
        enr.seq(record + b"\x00" * (enr.MAX_RECORD_SIZE + 1 - len(record)))


def test_text_without_prefix_rejected() -> None:
    with pytest.raises(ValueError):
        enr.from_text(TEXT[len("enr:"):])


def test_nonzero_pad_bits_rejected() -> None:
    # The last character goes from 8 to 9, which sets a bit past the end of the bytes.
    assert TEXT.endswith("8")
    with pytest.raises(ValueError, match="base64"):
        enr.from_text(TEXT[:-1] + "9")


def test_padded_text_rejected() -> None:
    with pytest.raises(ValueError):
        enr.from_text(TEXT + "=")
