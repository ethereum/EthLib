"""Era1 files, built in the test and pinned from the public pre-Merge history."""

# The layout follows formats/era1.md of eth-clients/e2store-format-specs at commit 31cf6b57:
# https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/formats/era1.md
# Where that document leaves the layout open, the built files take EthLib's reading.
# The pinned public file checks that reading.
# The test writes the records, the block index and the accumulator without EthLib.
# It takes only Keccak-256 and the Snappy framing from EthLib, which have suites of their own.

import dataclasses
import hashlib
from collections.abc import Sequence

import pytest

import archives
from ethlib.cryptography import keccak
from ethlib.errors import Era1Error
from ethlib.execution.history import Era1Block, decode_era1
from ethlib.networking import snappy
from raising import raises, raises_shape

VERSION = 0x6532
HEADER = 0x0300
BODY = 0x0400
RECEIPTS = 0x0500
TOTAL_DIFFICULTY = 0x0600
ACCUMULATOR = 0x0700
BLOCK_INDEX = 0x6632
UNKNOWN = 0x7777

# Era 0 of mainnet: blocks 0 to 8191.
# Its name carries the first 4 bytes of its accumulator.
ARCHIVE = "era1/mainnet-00000-5ec1ffb8"
MAINNET_GENESIS_HASH = "d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3"


def _rlp(item: bytes | list) -> bytes:
    """The RLP of a byte string or a list, from Appendix B of the Yellow Paper."""
    if isinstance(item, bytes):
        if len(item) == 1 and item[0] < 0x80:
            return item
        payload, short, long = item, 0x80, 0xB7
    else:
        payload, short, long = b"".join(_rlp(x) for x in item), 0xC0, 0xF7
    if len(payload) < 56:
        return bytes([short + len(payload)]) + payload
    size = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([long + len(size)]) + size + payload


def _scalar(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _header(parent: bytes, difficulty: int, number: int) -> bytes:
    """The RLP of a header of the fifteen fields before London."""
    return _rlp(
        [
            parent,
            keccak.keccak256(_rlp([])),
            bytes(20),
            bytes(32),
            bytes(32),
            bytes(32),
            bytes(256),
            _scalar(difficulty),
            _scalar(number),
            _scalar(5000),
            b"",
            _scalar(number),
            b"",
            bytes(32),
            bytes(8),
        ]
    )


def _record(type_: int, data: bytes) -> bytes:
    """An e2store record: a 2-byte type, a 4-byte little-endian length, 2 zero bytes, the data."""
    return type_.to_bytes(2, "big") + len(data).to_bytes(4, "little") + bytes(2) + data


def _int64(n: int) -> bytes:
    return n.to_bytes(8, "little", signed=True)


def _accumulator(blocks: list[tuple[bytes, int]]) -> bytes:
    """The SSZ root of a list of at most 8192 pairs of a block hash and a total difficulty."""
    nodes = [hashlib.sha256(h + td.to_bytes(32, "little")).digest() for h, td in blocks]
    zero = bytes(32)
    for _ in range(13):
        if len(nodes) % 2:
            nodes.append(zero)
        nodes = [
            hashlib.sha256(a + b).digest() for a, b in zip(nodes[::2], nodes[1::2], strict=True)
        ]
        zero = hashlib.sha256(zero + zero).digest()
    root = nodes[0] if nodes else zero
    return hashlib.sha256(root + len(blocks).to_bytes(32, "little")).digest()


def _chain(start: int, count: int) -> list[Era1Block]:
    """Blocks from the number `start`, each with difficulty 1000 more than its number."""
    blocks: list[Era1Block] = []
    # After genesis, the first total difficulty is free, so a later era starts from any total.
    parent, td = bytes(32), 0 if start == 0 else 10**9
    for number in range(start, start + count):
        header = _header(parent, 1000 + number, number)
        td += 1000 + number
        blocks.append(
            Era1Block(header=header, body=_rlp([[], []]), receipts=_rlp([]), total_difficulty=td)
        )
        parent = keccak.keccak256(header)
    return blocks


def _file(
    start: int,
    blocks: list[Era1Block],
    *,
    others: Sequence[tuple[int, bytes]] = (),
    accumulator: bytes | None = None,
    last_offset_shift: int = 0,
    count: int | None = None,
) -> bytes:
    """The bytes of an era1 file, with a block index that points at each header record."""
    out = _record(VERSION, b"")
    headers = []
    for block in blocks:
        headers.append(len(out))
        out += _record(HEADER, snappy.encode_frames(block.header))
        out += _record(BODY, snappy.encode_frames(block.body))
        out += _record(RECEIPTS, snappy.encode_frames(block.receipts))
        out += _record(TOTAL_DIFFICULTY, block.total_difficulty.to_bytes(32, "little"))
    for type_, data in others:
        out += _record(type_, data)
    if accumulator is None:
        accumulator = _accumulator(
            [(keccak.keccak256(b.header), b.total_difficulty) for b in blocks]
        )
    out += _record(ACCUMULATOR, accumulator)
    index_start = len(out)
    offsets = [h - index_start for h in headers]
    if offsets:
        offsets[-1] += last_offset_shift
    index = _int64(start) + b"".join(_int64(offset) for offset in offsets)
    index += _int64(len(blocks) if count is None else count)
    return out + _record(BLOCK_INDEX, index)


def _without_index(data: bytes, count: int) -> bytes:
    """The file without its BlockIndex record, which holds `count` offsets."""
    return data[: len(data) - 8 - (16 + 8 * count)]


def _error(fault: str) -> str:
    return f"era1 file rejected: EthLib.Execution.History.Era1Error.{fault}"


@pytest.mark.parametrize(("start", "count"), [(0, 0), (0, 1), (0, 5), (8192, 3)])
def test_valid_file_decodes_to_its_blocks(start: int, count: int) -> None:
    blocks = _chain(start, count)
    era1 = decode_era1(_file(start, blocks))
    assert era1.starting_number == start
    assert era1.blocks == tuple(blocks)
    assert era1.others == ()
    assert era1.accumulator == _accumulator(
        [(keccak.keccak256(b.header), b.total_difficulty) for b in blocks]
    )


def test_other_records_are_kept() -> None:
    blocks = _chain(0, 2)
    era1 = decode_era1(_file(0, blocks, others=[(UNKNOWN, b"x"), (0x0000, b"")]))
    assert era1.others == ((UNKNOWN, b"x"), (0x0000, b""))


def test_full_era_of_8192_blocks_decodes() -> None:
    blocks = _chain(0, 8192)
    assert decode_era1(_file(0, blocks)).blocks == tuple(blocks)


def test_one_block_too_many_is_rejected() -> None:
    blocks = _chain(0, 8193)
    with raises(Era1Error, _error("tooManyBlocks 8193")):
        decode_era1(_file(0, blocks, accumulator=bytes(32)))


def test_file_without_version_is_rejected() -> None:
    data = _file(0, _chain(0, 1))
    with raises(Era1Error, _error("e2store (EthLib.Serialization.E2store.E2storeError.noVersion)")):
        decode_era1(data[8:])


def test_file_without_index_is_rejected() -> None:
    data = _file(0, _chain(0, 1))
    with raises(Era1Error, _error("noTrailer")):
        decode_era1(_without_index(data, 1))


def test_cut_block_is_rejected() -> None:
    blocks = _chain(0, 2)
    # A lone header among the other records is a block cut short.
    lone = snappy.encode_frames(blocks[1].header)
    with raises(Era1Error, _error("misplacedRecord 768")):
        decode_era1(_file(0, blocks[:1], others=[(HEADER, lone)]))


def test_wrong_size_total_difficulty_is_rejected() -> None:
    block = _chain(0, 1)[0]
    out = _record(VERSION, b"") + _record(HEADER, snappy.encode_frames(block.header))
    out += _record(BODY, snappy.encode_frames(block.body))
    out += _record(RECEIPTS, snappy.encode_frames(block.receipts))
    out += _record(TOTAL_DIFFICULTY, bytes(31))
    out += _record(ACCUMULATOR, bytes(32))
    # The header record follows the Version record, which is 8 bytes.
    header_start = len(_record(VERSION, b""))
    index_start = len(out)
    out += _record(BLOCK_INDEX, _int64(0) + _int64(header_start - index_start) + _int64(1))
    with raises(Era1Error, _error("wrongSize 1536 31")):
        decode_era1(out)


def test_wrong_size_accumulator_is_rejected() -> None:
    with raises(Era1Error, _error("wrongSize 1792 31")):
        decode_era1(_file(0, _chain(0, 2), accumulator=bytes(31)))


@pytest.mark.parametrize("count", [1, 3])
def test_wrong_block_count_is_rejected(count: int) -> None:
    data = _without_index(_file(0, _chain(0, 2)), 2)
    index = _int64(0) + _int64(0) * count + _int64(count)
    with raises(Era1Error, _error(f"blockCount {count} 2")):
        decode_era1(data + _record(BLOCK_INDEX, index))


def test_index_of_wrong_size_is_rejected() -> None:
    data = _file(0, _chain(0, 2))
    index = data[len(data) - (16 + 8 * 2) :] + bytes(1)
    with raises(Era1Error, _error("e2store (EthLib.Serialization.E2store.E2storeError.indexSize)")):
        decode_era1(_without_index(data, 2) + _record(BLOCK_INDEX, index))


@pytest.mark.parametrize("shift", [-1, 1, 8])
def test_offset_off_its_header_is_rejected(shift: int) -> None:
    with raises(Era1Error, _error("blockOffset 2")):
        decode_era1(_file(0, _chain(0, 3), last_offset_shift=shift))


def test_bad_frame_is_rejected() -> None:
    blocks = _chain(0, 2)
    data = bytearray(_file(0, blocks))
    # Flip a bit of the checksum of the first data chunk of the second body record.
    tag = _record(BODY, snappy.encode_frames(blocks[1].body))[:8]
    body = data.index(tag, data.index(tag) + 1)
    data[body + 8 + 10 + 4] ^= 1
    with raises_shape(
        Era1Error,
        _error("frame 1 (EthLib.Networking.Snappy.FrameError.checksumMismatch {n} {n})"),
    ):
        decode_era1(bytes(data))


def test_body_that_is_not_one_item_is_rejected() -> None:
    blocks = _chain(0, 2)
    blocks[1] = dataclasses.replace(blocks[1], body=_rlp([]) + b"\x00")
    with raises(Era1Error, _error("rlp 1 (EthLib.Serialization.Rlp.RlpError.trailingBytes 1)")):
        decode_era1(_file(0, blocks))


def test_receipts_that_are_not_one_item_are_rejected() -> None:
    blocks = _chain(0, 2)
    blocks[0] = dataclasses.replace(blocks[0], receipts=b"")
    with raises(Era1Error, _error("rlp 0 (EthLib.Serialization.Rlp.RlpError.inputTooShort 1 0)")):
        decode_era1(_file(0, blocks))


def test_header_with_too_few_fields_is_rejected() -> None:
    blocks = _chain(0, 1)
    # A list of 7 fields has neither a difficulty nor a number, the ninth field.
    blocks[0] = dataclasses.replace(blocks[0], header=_rlp([bytes(32)] * 7))
    with raises(Era1Error, _error("rlp 0 (EthLib.Serialization.Rlp.RlpError.wrongFieldCount 9 7)")):
        decode_era1(_file(0, blocks))


def test_wrong_start_is_rejected() -> None:
    with raises(Era1Error, _error("blockNumber 0")):
        decode_era1(_file(1, _chain(0, 3)))


def test_wrong_number_is_rejected() -> None:
    blocks = _chain(0, 3)
    # The last header keeps its parent link but carries the number 3.
    header = _header(keccak.keccak256(blocks[1].header), 1002, 3)
    blocks[2] = dataclasses.replace(blocks[2], header=header)
    with raises(Era1Error, _error("blockNumber 2")):
        decode_era1(_file(0, blocks))


def test_broken_parent_link_is_rejected() -> None:
    blocks = _chain(0, 3)
    header = _header(bytes(32), 1002, 2)
    blocks[2] = dataclasses.replace(blocks[2], header=header)
    with raises(Era1Error, _error("parentHash 2")):
        decode_era1(_file(0, blocks))


@pytest.mark.parametrize(("index", "start"), [(0, 0), (2, 0), (1, 100)])
def test_wrong_total_difficulty_is_rejected(index: int, start: int) -> None:
    blocks = _chain(start, 3)
    block = blocks[index]
    blocks[index] = dataclasses.replace(block, total_difficulty=block.total_difficulty + 1)
    with raises(Era1Error, _error(f"totalDifficulty {index}")):
        decode_era1(_file(start, blocks))


def test_first_total_difficulty_after_genesis_is_free() -> None:
    blocks = _chain(100, 1)
    blocks[0] = dataclasses.replace(blocks[0], total_difficulty=blocks[0].total_difficulty + 7)
    assert decode_era1(_file(100, blocks)).blocks == tuple(blocks)


def test_wrong_accumulator_is_rejected() -> None:
    with raises(Era1Error, _error("accumulator")):
        decode_era1(_file(0, _chain(0, 2), accumulator=bytes(32)))


def test_argument_of_wrong_type_is_rejected() -> None:
    with raises(Era1Error, "expected bytes"):
        decode_era1("era1")  # ty: ignore[invalid-argument-type]


@pytest.mark.archive(ARCHIVE)
def test_mainnet_era_0() -> None:
    data = archives.download(ARCHIVE).read_bytes()
    era1 = decode_era1(data)
    assert era1.starting_number == 0
    assert len(era1.blocks) == 8192
    assert era1.accumulator.hex().startswith("5ec1ffb8")
    assert keccak.keccak256(era1.blocks[0].header).hex() == MAINNET_GENESIS_HASH
    # The genesis difficulty is 2^34.
    assert era1.blocks[0].total_difficulty == 2**34
    assert era1.accumulator == _accumulator(
        [(keccak.keccak256(b.header), b.total_difficulty) for b in era1.blocks]
    )
