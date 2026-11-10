"""Era files, built in the test from the blocks and states of the ssz_static vectors."""

# The layout follows formats/era.md of eth-clients/e2store-format-specs at commit 31cf6b57:
# https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/formats/era.md
# No public era file is pinned: none is served from a host that names no implementation.
# The test writes the records, the indices and the block roots without EthLib.
# It takes the block bodies and the states from the vendored ssz_static vectors of consensus-specs.
# Each state gets the slot, the fork version and the block roots of its era, at fixed offsets.
# It takes only Snappy from EthLib: the framing, and the blocks that hold the vectors.
# Each has a suite of its own.

import dataclasses
import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.consensus.history import EraError, EraFile, decode_era
from ethlib.networking import snappy
from raising import raises

VECTORS = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "ssz_static" / "minimal"

VERSION = 0x6532
BLOCK = 0x0100
STATE = 0x0200
SLOT_INDEX = 0x6932
UNKNOWN = 0x7777

# The minimal preset: 8 slots per epoch, 64 slots per era.
SLOTS_PER_EPOCH = 8
SLOTS_PER_ERA = 64

# Phase 0 until epoch 8, then Altair, Bellatrix from epoch 12, and Capella from epoch 16.
# So era 1 holds Phase 0 blocks and an Altair state, and era 2 holds blocks of two forks.
CONFIG = {"ALTAIR_FORK_EPOCH": 8, "BELLATRIX_FORK_EPOCH": 12, "CAPELLA_FORK_EPOCH": 16}
FORKS = [(16, "capella", "shapella"), (12, "bellatrix", "bellatrix"), (8, "altair", "altair")]
VERSIONS = {"phase0": 0, "altair": 1, "bellatrix": 2, "capella": 3}

# Where a state of every fork holds its slot, the version of its fork, and its block roots.
SLOT_AT = 40
CURRENT_VERSION_AT = 52
BLOCK_ROOTS_AT = 176
# The offset of the historical roots, after the block roots and the state roots.
HISTORICAL_ROOTS_AT = BLOCK_ROOTS_AT + 2 * 32 * SLOTS_PER_ERA


def _fork(slot: int) -> tuple[str, str]:
    """The fork of a slot: its directory in the vectors and its name in EthLib."""
    for epoch, directory, name in FORKS:
        if slot // SLOTS_PER_EPOCH >= epoch:
            return directory, name
    return "phase0", "phase0"


def _vector(fork: str, container: str) -> tuple[bytes, bytes]:
    """The bytes and the root of the ssz_one case, in which each list holds one element."""
    case = VECTORS / fork / "ssz_static" / container / "ssz_one" / "case_0"
    data = snappy.decompress((case / "serialized.ssz_snappy").read_bytes())
    root = YAML(typ="safe").load((case / "roots.yaml").read_text())["root"]
    return data, bytes.fromhex(root.removeprefix("0x"))


def _sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def _block_root(slot: int, proposer: int, parent: bytes, state_root: bytes, body: bytes) -> bytes:
    """The root of a block of five fields, padded to eight leaves."""
    leaves = [
        slot.to_bytes(32, "little"),
        proposer.to_bytes(32, "little"),
        parent,
        state_root,
        body,
        *[bytes(32)] * 3,
    ]
    while len(leaves) > 1:
        leaves = [_sha256(a + b) for a, b in zip(leaves[::2], leaves[1::2], strict=True)]
    return leaves[0]


@dataclasses.dataclass(frozen=True, slots=True)
class Block:
    """A signed block built in the test, with its root."""

    slot: int
    fork: str
    data: bytes
    root: bytes


def _block(slot: int, *, slot_field: int | None = None) -> Block:
    """A signed block at the slot, with the body of the vector of its fork and a zero signature."""
    directory, name = _fork(slot)
    body, body_root = _vector(directory, "BeaconBlockBody")
    written = slot if slot_field is None else slot_field
    parent, state_root = bytes([1]) * 32, bytes([2]) * 32
    # The block: slot, proposer, parent root, state root, then the offset of the body, 84.
    message = written.to_bytes(8, "little") + (7).to_bytes(8, "little") + parent + state_root
    message += (84).to_bytes(4, "little") + body
    # The signed block: the offset of the message, 100, then the signature.
    data = (100).to_bytes(4, "little") + bytes(96) + message
    return Block(slot, name, data, _block_root(written, 7, parent, state_root, body_root))


def _state(slot: int, block_roots: list[bytes]) -> tuple[str, bytes]:
    """A state of the fork of the slot, at the slot, with its version and the block roots."""
    directory, name = _fork(slot)
    path = VECTORS / directory / "ssz_static" / "BeaconState" / "ssz_one" / "case_0"
    state = bytearray(snappy.decompress((path / "serialized.ssz_snappy").read_bytes()))
    state[SLOT_AT : SLOT_AT + 8] = slot.to_bytes(8, "little")
    state[CURRENT_VERSION_AT : CURRENT_VERSION_AT + 4] = bytes([VERSIONS[directory], 0, 0, 1])
    for i, root in enumerate(block_roots):
        state[BLOCK_ROOTS_AT + 32 * i : BLOCK_ROOTS_AT + 32 * (i + 1)] = root
    return name, bytes(state)


def _record(type_: int, data: bytes) -> bytes:
    """An e2store record: a 2-byte type, a 4-byte little-endian length, 2 zero bytes, the data."""
    return type_.to_bytes(2, "big") + len(data).to_bytes(4, "little") + bytes(2) + data


def _index(start: int, offsets: list[int]) -> bytes:
    """The data of a SlotIndex record: the first slot, each offset, then the count."""
    fields = [start, *offsets, len(offsets)]
    return b"".join(n.to_bytes(8, "little", signed=True) for n in fields)


def _roots(first: int, blocks: list[Block]) -> list[bytes]:
    """The block roots of the era from the slot `first`, by slot modulo the era length."""
    by_slot = {block.slot: block.root for block in blocks}
    # The root before the first block of the era is that of a block of the era before.
    root, roots = bytes([0xAA]) * 32, []
    for slot in range(first, first + SLOTS_PER_ERA):
        root = by_slot.get(slot, root)
        roots.append(root)
    return roots


@dataclasses.dataclass(frozen=True, slots=True)
class Group:
    """What a test asks of one group: its era, its blocks and the changes to make."""

    era: int
    blocks: list[Block] = dataclasses.field(default_factory=list)
    others: list[tuple[int, bytes]] = dataclasses.field(default_factory=list)
    roots: list[bytes] | None = None
    # The slot of the state, and of its index, after the end of the era.
    slot_shift: int = 0
    drop_block_index: bool = False
    block_start_shift: int = 0
    # Entries of 0 after the last slot of the era.
    extra_entries: int = 0
    shift: dict[int, int] = dataclasses.field(default_factory=dict)
    unindexed: set[int] = dataclasses.field(default_factory=set)
    # Slots without a block whose entry is not 0.
    phantom: set[int] = dataclasses.field(default_factory=set)
    state_index_start: int | None = None
    state_offset_shift: int = 0
    version: bytes | None = None
    historical_root: bytes | None = None


def _group(group: Group, at: int) -> tuple[bytes, bytes]:
    """The bytes of a group whose Version record starts at `at`, and the bytes of its state."""
    slot = group.era * SLOTS_PER_ERA + group.slot_shift
    first = slot - SLOTS_PER_ERA
    roots = _roots(first, group.blocks) if group.roots is None else group.roots
    _, state = _state(slot, roots if group.era else [])
    if group.version is not None:
        state = state[:CURRENT_VERSION_AT] + group.version + state[CURRENT_VERSION_AT + 4 :]
    if group.historical_root is not None:
        at_root = int.from_bytes(state[HISTORICAL_ROOTS_AT : HISTORICAL_ROOTS_AT + 4], "little")
        state = state[:at_root] + group.historical_root + state[at_root + 32 :]
    out = _record(VERSION, b"")
    starts = {}
    for block in group.blocks:
        starts[block.slot] = at + len(out)
        out += _record(BLOCK, snappy.encode_frames(block.data))
    state_at = at + len(out)
    out += _record(STATE, snappy.encode_frames(state))
    for type_, data in group.others:
        out += _record(type_, data)
    if group.era > 0 and not group.drop_block_index:
        index_at = at + len(out)
        offsets = [
            starts[s] - index_at + group.shift.get(s, 0)
            if s in starts and s not in group.unindexed
            else 1
            if s in group.phantom
            else 0
            for s in range(first, first + SLOTS_PER_ERA)
        ]
        offsets += [0] * group.extra_entries
        out += _record(SLOT_INDEX, _index(first + group.block_start_shift, offsets))
    index_at = at + len(out)
    start = slot if group.state_index_start is None else group.state_index_start
    out += _record(SLOT_INDEX, _index(start, [state_at - index_at + group.state_offset_shift]))
    return out, state


def _file(*groups: Group) -> tuple[bytes, list[bytes]]:
    """The bytes of a file of the groups, and the bytes of the state of each."""
    out, states = b"", []
    for group in groups:
        data, state = _group(group, len(out))
        out += data
        states.append(state)
    return out, states


def _decode(data: bytes) -> EraFile:
    return decode_era("minimal", data, CONFIG)


def _error(fault: str) -> str:
    return f"era file rejected: EthLib.Consensus.History.EraError.{fault}"


def _historical_roots(state: bytes) -> bytes:
    """The bytes of the historical roots of a state of one root, from their offset."""
    start = int.from_bytes(state[HISTORICAL_ROOTS_AT : HISTORICAL_ROOTS_AT + 4], "little")
    return state[start : start + 32]


ERA_1_BLOCKS = [1, 2, 5, 63]
ERA_2_BLOCKS = [64, 100, 127]


def test_genesis_group_names_the_file_by_the_genesis_validators_root() -> None:
    data, (state,) = _file(Group(0))
    era = _decode(data)
    (group,) = era.groups
    assert (group.era, group.blocks, group.state_fork, group.state) == (0, (), "phase0", state)
    # The genesis validators root follows the 8 bytes of the genesis time.
    assert era.name == f"minimal-00000-{state[8:12].hex()}.era"


def test_era_1_has_its_blocks_and_its_state() -> None:
    blocks = [_block(slot) for slot in ERA_1_BLOCKS]
    data, (state,) = _file(Group(1, blocks))
    era = _decode(data)
    (group,) = era.groups
    assert group.era == 1
    assert group.state == state
    assert group.state_fork == "altair"
    assert [(b.slot, b.fork, b.block, b.root) for b in group.blocks] == [
        (b.slot, b.fork, b.data, b.root) for b in blocks
    ]
    # Before Capella, the root of era 1 is the first historical root.
    assert era.name == f"minimal-00001-{_historical_roots(state)[:4].hex()}.era"


def test_blocks_of_two_forks_in_one_era() -> None:
    blocks = [_block(slot) for slot in ERA_2_BLOCKS]
    era = _decode(_file(Group(2, blocks))[0])
    (group,) = era.groups
    assert [(b.slot, b.fork) for b in group.blocks] == [
        (64, "altair"),
        (100, "bellatrix"),
        (127, "bellatrix"),
    ]
    assert group.state_fork == "shapella"


def test_capella_state_after_its_one_historical_root_names_by_its_summary() -> None:
    data, (state,) = _file(Group(2, [_block(slot) for slot in ERA_2_BLOCKS]))
    # The summary of era 1 is the last field, 64 bytes; its root hashes its two roots.
    root = _sha256(state[-64:])
    assert _decode(data).name == f"minimal-00002-{root[:4].hex()}.era"


def test_groups_name_the_file_by_the_lowest_era_and_the_root_of_the_highest() -> None:
    data, states = _file(
        Group(2, [_block(slot) for slot in ERA_2_BLOCKS]),
        Group(0),
        Group(1, [_block(slot) for slot in ERA_1_BLOCKS]),
    )
    era = _decode(data)
    assert [group.era for group in era.groups] == [2, 0, 1]
    assert [group.state for group in era.groups] == states
    assert era.name == f"minimal-00000-{_sha256(states[0][-64:])[:4].hex()}.era"


def test_state_without_root_for_its_era_leaves_no_name() -> None:
    # The Capella state of era 3 has one historical root and one summary, so none for era 2.
    data, _ = _file(Group(3))
    assert _decode(data).name is None


def test_era_of_empty_slots_only() -> None:
    (group,) = _decode(_file(Group(1))[0]).groups
    assert group.blocks == ()


def test_other_records_are_kept() -> None:
    others = [(UNKNOWN, b"x"), (0x0000, b"")]
    (group,) = _decode(_file(Group(1, [_block(1)], others=others))[0]).groups
    assert group.others == tuple(others)


def test_truncated_file_is_rejected() -> None:
    data, _ = _file(Group(0))
    with raises(
        EraError, _error("e2store (EthLib.Serialization.E2store.E2storeError.truncatedData)")
    ):
        _decode(data[:-1])


def test_group_without_state_is_rejected() -> None:
    data = _record(VERSION, b"") + _record(SLOT_INDEX, _index(0, [0]))
    with raises(EraError, _error("noState")):
        _decode(data)


def test_group_without_state_index_is_rejected() -> None:
    data, _ = _file(Group(0))
    with raises(EraError, _error("noStateIndex")):
        _decode(data[: len(data) - 32])


def test_record_of_the_era_document_among_the_others_is_rejected() -> None:
    with raises(EraError, _error("misplacedRecord 256")):
        _decode(_file(Group(0, others=[(BLOCK, b"")]))[0])


@pytest.mark.parametrize("shift", [-1, 8])
def test_state_index_off_the_state_is_rejected(shift: int) -> None:
    with raises(EraError, _error("stateIndex")):
        _decode(_file(Group(0, state_offset_shift=shift))[0])


def test_state_that_is_not_framed_is_rejected() -> None:
    data = _record(VERSION, b"") + _record(STATE, b"\x00")
    data += _record(SLOT_INDEX, _index(0, [-(len(data) - 8)]))
    with raises(
        EraError,
        _error("frame 0 (EthLib.Networking.Snappy.FrameError.missingStreamIdentifier)"),
    ):
        _decode(data)


def test_block_that_does_not_decode_is_rejected() -> None:
    block = _block(1)
    broken = dataclasses.replace(block, data=block.data[:50])
    with raises(EraError, _error("ssz 1 (EthLib.Serialization.Ssz.Err.scopeTooSmall 100 50)")):
        _decode(_file(Group(1, [broken]))[0])


def test_state_off_the_last_slot_of_an_era_is_rejected() -> None:
    with raises(EraError, _error("stateSlot 65")):
        _decode(_file(Group(1, state_index_start=65))[0])


def test_state_of_the_wrong_fork_version_is_rejected() -> None:
    with raises(EraError, _error("forkVersion 64")):
        _decode(_file(Group(1, version=bytes([0, 0, 0, 1])))[0])


def test_genesis_group_with_a_block_is_rejected() -> None:
    with raises(EraError, _error("genesisBlocks")):
        _decode(_file(Group(0, [_block(0)]))[0])


def test_genesis_group_with_a_block_index_is_rejected() -> None:
    data = _record(VERSION, b"")
    data += _record(STATE, snappy.encode_frames(_state(0, [])[1]))
    data += _record(SLOT_INDEX, _index(0, [0]))
    data += _record(SLOT_INDEX, _index(0, [-(len(data) - 8)]))
    with raises(EraError, _error("genesisBlocks")):
        _decode(data)


def test_group_without_block_index_is_rejected() -> None:
    with raises(EraError, _error("noBlockIndex")):
        _decode(_file(Group(1, drop_block_index=True))[0])


def test_block_index_of_another_era_is_rejected() -> None:
    with raises(EraError, _error("blockIndexRange")):
        _decode(_file(Group(1, block_start_shift=1))[0])


@pytest.mark.parametrize("shift", [-1, 1])
def test_offset_off_its_block_is_rejected(shift: int) -> None:
    blocks = [_block(slot) for slot in ERA_1_BLOCKS]
    with raises(EraError, _error("blockOffset 5")):
        _decode(_file(Group(1, blocks, shift={5: shift}))[0])


def test_block_out_of_slot_order_is_rejected() -> None:
    blocks = [_block(2), _block(1)]
    with raises(EraError, _error("blockOffset 1")):
        _decode(_file(Group(1, blocks))[0])


def test_block_that_no_slot_points_at_is_rejected() -> None:
    blocks = [_block(1), _block(2)]
    # The second block record follows the Version record and the first block record.
    position = 8 + len(_record(BLOCK, snappy.encode_frames(blocks[0].data)))
    with raises(EraError, _error(f"unindexedBlock {position}")):
        _decode(_file(Group(1, blocks, unindexed={2}))[0])


def test_block_of_another_slot_is_rejected() -> None:
    block = _block(2, slot_field=3)
    with raises(EraError, _error("blockSlot 2")):
        _decode(_file(Group(1, [block]))[0])


def test_block_of_another_root_is_rejected() -> None:
    blocks = [_block(1), _block(2)]
    roots = _roots(0, blocks)
    roots[2] = bytes([0xBB]) * 32
    with raises(EraError, _error("blockRoot 2")):
        _decode(_file(Group(1, blocks, roots=roots))[0])


def test_empty_slot_with_a_new_root_is_rejected() -> None:
    blocks = [_block(1)]
    roots = _roots(0, blocks)
    roots[3] = bytes([0xBB]) * 32
    with raises(EraError, _error("emptySlot 3")):
        _decode(_file(Group(1, blocks, roots=roots))[0])


def test_empty_file_is_rejected() -> None:
    with raises(EraError, _error("e2store (EthLib.Serialization.E2store.E2storeError.noVersion)")):
        _decode(b"")


def test_empty_group_is_rejected() -> None:
    with raises(EraError, _error("noState")):
        _decode(_record(VERSION, b""))


def test_state_with_its_index_off_the_end_of_an_era_is_rejected() -> None:
    # The state and both indices agree on slot 65, which ends no era.
    with raises(EraError, _error("stateSlot 65")):
        _decode(_file(Group(1, slot_shift=1))[0])


def test_state_index_of_two_entries_is_rejected() -> None:
    data = _record(VERSION, b"") + _record(STATE, snappy.encode_frames(_state(0, [])[1]))
    data += _record(SLOT_INDEX, _index(0, [-(len(data) - 8), 0]))
    with raises(EraError, _error("stateIndex")):
        _decode(data)


def test_state_that_does_not_decode_is_rejected() -> None:
    data = _record(VERSION, b"") + _record(STATE, snappy.encode_frames(b"\x00"))
    data += _record(SLOT_INDEX, _index(0, [-(len(data) - 8)]))
    with raises(EraError, _error("ssz 0 (EthLib.Serialization.Ssz.Err.scopeTooSmall 7057 1)")):
        _decode(data)


def test_index_of_the_wrong_size_is_rejected() -> None:
    data = _record(VERSION, b"") + _record(STATE, snappy.encode_frames(_state(0, [])[1]))
    data += _record(SLOT_INDEX, _index(0, [-(len(data) - 8)])[:-1])
    with raises(EraError, _error("e2store (EthLib.Serialization.E2store.E2storeError.indexSize)")):
        _decode(data)


def test_block_index_of_more_entries_than_slots_is_rejected() -> None:
    with raises(EraError, _error("blockIndexRange")):
        _decode(_file(Group(1, extra_entries=1))[0])


def test_entry_without_a_block_record_left_is_rejected() -> None:
    with raises(EraError, _error("blockOffset 3")):
        _decode(_file(Group(1, [_block(1)], phantom={3}))[0])


def test_later_group_of_the_highest_era_names_the_file() -> None:
    first, second = bytes([0x11]) * 32, bytes([0x22]) * 32
    data, _ = _file(Group(1, historical_root=first), Group(1, historical_root=second))
    assert _decode(data).name == f"minimal-00001-{second[:4].hex()}.era"


def test_unknown_preset_is_rejected() -> None:
    with raises(EraError, "no preset is named sepolia"):
        decode_era("sepolia", b"")
