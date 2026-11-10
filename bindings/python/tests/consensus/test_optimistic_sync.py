"""The optimistic sync of Bellatrix and Gloas against blocks built in the test or from vectors."""

import struct
from collections.abc import Sequence
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

ERROR = consensus.ForkChoiceError
FORK = "bellatrix"
ZERO = bytes(32)

# The mainnet sizes of the fixed part of a Bellatrix payload, body and block.
PAYLOAD_FIXED = 32 + 20 + 32 + 32 + 256 + 32 + 8 * 4 + 4 + 32 + 32 + 4
BODY_FIXED = 96 + 72 + 32 + 5 * 4 + 64 + 96 + 4
BLOCK_FIXED = 8 + 8 + 32 + 32 + 4


def payload(block_number: int) -> bytes:
    """A payload whose fields are zero but its block number; number 0 gives the empty payload."""
    return (
        bytes(32 + 20 + 32 + 32 + 256 + 32)
        + struct.pack("<QQQQ", block_number, 0, 0, 0)
        + struct.pack("<I", PAYLOAD_FIXED)
        + bytes(32 + 32)
        + struct.pack("<I", PAYLOAD_FIXED)
    )


def block(slot: int, parent: bytes, block_number: int = 0) -> bytes:
    """A mainnet Bellatrix block of a slot on a parent, with an empty body but its payload."""
    body = bytes(96 + 72 + 32) + struct.pack("<I", BODY_FIXED) * 5 + bytes(64 + 96)
    body += struct.pack("<I", BODY_FIXED) + payload(block_number)
    head = struct.pack("<QQ", slot, 0) + parent + bytes(32) + struct.pack("<I", BLOCK_FIXED)
    return head + body


def root(data: bytes) -> bytes:
    """The root of a block, from the SSZ export, which also checks that the bytes decode."""
    found, again = consensus.ssz_static("mainnet", FORK, "BeaconBlock", data)
    assert again == data
    return found


# A genesis block g without payload, then a with a payload and b on it, and c on g.
G = block(1, ZERO)
A = block(2, root(G), 1)
B = block(3, root(A), 2)
C = block(3, root(G))
BLOCKS = [G, A, B, C]
RG, RA, RB, RC = (root(x) for x in BLOCKS)


def test_execution_block():
    assert not consensus.is_execution_block("mainnet", FORK, G)
    assert consensus.is_execution_block("mainnet", FORK, A)


@pytest.mark.parametrize(
    ("current_slot", "candidate", "expected"),
    [
        # The parent carries a payload, so the slot of the clock does not matter.
        (3, B, True),
        # The parent carries none: the block needs a slot at least 128 slots ago.
        (3 + 127, C, False),
        (3 + 128, C, True),
    ],
    ids=["parent payload", "too early", "far enough"],
)
def test_optimistic_candidate(current_slot: int, candidate: bytes, expected: bool):
    got = consensus.is_optimistic_candidate_block("mainnet", FORK, BLOCKS, current_slot, candidate)
    assert got is expected


def test_optimistic_candidate_with_another_number_of_slots():
    assert consensus.is_optimistic_candidate_block("mainnet", FORK, BLOCKS, 5, C, safe_slots=2)


@pytest.mark.parametrize(
    ("candidate", "code"),
    [(block(3, bytes([7]) * 32), 2), (block(2**64 - 1, RG), 7)],
    ids=["unknown parent", "overflow"],
)
def test_optimistic_candidate_rejected(candidate: bytes, code: int):
    with raises(ERROR, f"optimistic sync failed with code {code}") as info:
        consensus.is_optimistic_candidate_block("mainnet", FORK, BLOCKS, 0, candidate)
    assert info.value.code == code


@pytest.mark.parametrize(
    ("optimistic", "start", "expected"),
    [
        ([RA, RB], RB, RG),
        ([RA, RB], RG, RG),
        ([RA], RB, RB),
        # The walk stops at a block whose parent root is zero, optimistic or not.
        ([RG, RA, RB], RB, RG),
    ],
    ids=["two optimistic", "verified", "head verified", "genesis"],
)
def test_latest_verified_ancestor(optimistic: list, start: bytes, expected: bytes):
    assert (
        consensus.latest_verified_ancestor("mainnet", FORK, BLOCKS, optimistic, start) == expected
    )


def test_latest_verified_ancestor_rejected():
    orphan = block(4, bytes([7]) * 32)
    with raises(ERROR, "optimistic sync failed with code 2") as info:
        consensus.latest_verified_ancestor("mainnet", FORK, BLOCKS, [], bytes([9]) * 32)
    assert info.value.code == 2
    with raises(ERROR, "optimistic sync failed with code 2"):
        consensus.latest_verified_ancestor("mainnet", FORK, [orphan], [root(orphan)], root(orphan))


@pytest.mark.parametrize(
    ("valid", "expected"), [(RB, [RC]), (RA, [RB, RC]), (RC, [RA, RB])], ids=["b", "a", "c"]
)
def test_valid_payload(valid: bytes, expected: list):
    # The block and its ancestors leave the set.
    assert consensus.on_valid_payload("mainnet", FORK, BLOCKS, [RA, RB, RC], valid) == expected


@pytest.mark.parametrize(
    ("first", "expected"),
    [(RA, [RC]), (RB, [RA, RC]), (bytes([9]) * 32, [RA, RB, RC])],
    ids=["a", "b", "unknown"],
)
def test_invalidated_payload(first: bytes, expected: list):
    # The first invalid block and its descendants leave the set.
    assert (
        consensus.on_invalidated_payload("mainnet", FORK, BLOCKS, [RA, RB, RC], first) == expected
    )


def test_transitions_rejected():
    lower = block(1, RB)
    with raises(ERROR, "optimistic sync failed with code 6") as info:
        consensus.on_valid_payload("mainnet", FORK, [*BLOCKS, lower], [], root(lower))
    assert info.value.code == 6
    with raises(ERROR, "optimistic sync failed with code 2") as info:
        consensus.on_invalidated_payload("mainnet", FORK, BLOCKS, [bytes([9]) * 32], RA)
    assert info.value.code == 2


# A Gloas block of the minimal preset, from the consensus-specs vectors of tests/sources.toml.
GLOAS_FORK = "glamsterdam"
GLOAS_ANCHOR = snappy.decompress(
    (
        Path(__file__).resolve().parents[4]
        / "tests/consensus/fork_choice/minimal/gloas/fork_choice/on_block/pyspec_tests"
        / "on_block_parent_full_accepts_verified_payload/anchor_block.ssz_snappy"
    ).read_bytes()
)

# The Gloas body of the minimal preset: where the offset of the signed bid sits in its fixed part.
# Before it come the randao reveal, the eth1 data, the graffiti and five offsets.
# Then the sync aggregate of 4 + 96 bytes for 32 members, and the offset of the credential changes.
BID_OFFSET = 96 + 72 + 32 + 5 * 4 + 4 + 96 + 4
# A signed bid starts with the offset of its message and the signature.
BID_MESSAGE = 4 + 96


def gloas_block(slot: int, parent: bytes, parent_hash: int, block_hash: int) -> bytes:
    """A minimal Gloas block of a slot on a parent, whose bid names two block hashes."""
    data = bytearray(GLOAS_ANCHOR)
    data[0:8] = struct.pack("<Q", slot)
    data[16:48] = parent
    body = struct.unpack_from("<I", data, 8 + 8 + 32 + 32)[0]
    bid = body + struct.unpack_from("<I", data, body + BID_OFFSET)[0] + BID_MESSAGE
    assert struct.unpack_from("<I", data, bid - BID_MESSAGE)[0] == BID_MESSAGE
    # The bid holds the parent block hash, the parent block root, then the block hash.
    # Its other fields keep the values of the anchor, which no rule under test reads.
    data[bid : bid + 32] = bytes([parent_hash]) * 32
    data[bid + 64 : bid + 96] = bytes([block_hash]) * 32
    return bytes(data)


def gloas_root(data: bytes) -> bytes:
    """The root of a minimal Gloas block, which also checks that the bytes decode."""
    found, again = consensus.ssz_static("minimal", GLOAS_FORK, "BeaconBlock", data)
    assert again == data
    return found


# The block g names hash 1; a builds on its payload, and names hash 2.
# Then b builds on a without its payload, so on hash 1, and c builds on the payload of b.
# The block z names the zero hash; the late candidates below build on it.
GLOAS_G = gloas_block(1, ZERO, 0, 1)
GLOAS_A = gloas_block(2, gloas_root(GLOAS_G), 1, 2)
GLOAS_B = gloas_block(3, gloas_root(GLOAS_A), 1, 3)
GLOAS_C = gloas_block(4, gloas_root(GLOAS_B), 3, 4)
GLOAS_Z = gloas_block(1, ZERO, 0, 0)
GLOAS_BLOCKS = [GLOAS_G, GLOAS_A, GLOAS_B, GLOAS_C, GLOAS_Z]
GG, GA, GB, GC, GZ = (gloas_root(x) for x in GLOAS_BLOCKS)


def test_gloas_execution_block():
    assert consensus.is_execution_block("minimal", GLOAS_FORK, GLOAS_G)
    assert not consensus.is_execution_block("minimal", GLOAS_FORK, GLOAS_Z)


@pytest.mark.parametrize(
    ("current_slot", "candidate", "expected"),
    [
        # The bid of the parent names a payload, so the block is a candidate at once.
        (2, gloas_block(2, GG, 1, 5), True),
        # The bid of the parent names the zero hash: the block waits 128 slots.
        (2 + 127, gloas_block(2, GZ, 0, 5), False),
        (2 + 128, gloas_block(2, GZ, 0, 5), True),
    ],
    ids=["parent payload", "too early", "far enough"],
)
def test_gloas_optimistic_candidate(current_slot: int, candidate: bytes, expected: bool):
    got = consensus.is_optimistic_candidate_block(
        "minimal", GLOAS_FORK, GLOAS_BLOCKS, current_slot, candidate
    )
    assert got is expected


@pytest.mark.parametrize(
    ("valid", "expected"),
    [
        # The payload of c builds on those of b and g, and not on the payload of a.
        (GC, [GA]),
        (GB, [GA, GC]),
        (GA, [GB, GC]),
    ],
    ids=["c", "b", "a"],
)
def test_gloas_valid_payload(valid: bytes, expected: list[bytes]):
    optimistic = [GG, GA, GB, GC]
    got = consensus.on_valid_payload("minimal", GLOAS_FORK, GLOAS_BLOCKS, optimistic, valid)
    assert got == expected


@pytest.mark.parametrize(
    ("first", "expected"),
    [
        # The blocks b and c descend from a, but their payloads do not build on its payload.
        (GA, [GG, GB, GC]),
        (GB, [GG, GA]),
        (GG, []),
    ],
    ids=["a", "b", "g"],
)
def test_gloas_invalidated_payload(first: bytes, expected: list[bytes]):
    optimistic = [GG, GA, GB, GC]
    got = consensus.on_invalidated_payload("minimal", GLOAS_FORK, GLOAS_BLOCKS, optimistic, first)
    assert got == expected


RESTRICTED = [0, 1, 5, 6, 7, 8, 9]


@pytest.mark.parametrize("kind", range(17))
def test_restricted_domains(kind: int):
    expected = kind in RESTRICTED
    assert consensus.is_optimistic_restricted_domain(bytes([kind, 0, 0, 0])) is expected


def test_restricted_domain_of_another_length():
    with raises(ERROR, "a domain type is 4 bytes, not 3") as info:
        consensus.is_optimistic_restricted_domain(bytes(3))
    assert info.value.code == 0


# A case of the consensus-specs optimistic sync vectors, pinned in tests/sources.toml.
SYNC_CASE = (
    Path(__file__).resolve().parents[4]
    / "tests/consensus/fork_choice/minimal/bellatrix/sync/optimistic/pyspec_tests"
    / "from_syncing_to_invalid"
)


def _case_file(name: str) -> bytes:
    """The SSZ bytes of a file of the case, without the Snappy framing."""
    return snappy.decompress((SYNC_CASE / f"{name}.ssz_snappy").read_bytes())


def _case_steps() -> list[consensus.ForkChoiceStep]:
    """The ticks, blocks and payload verdicts of the case, as fork choice steps."""
    steps: list[consensus.ForkChoiceStep] = []
    for step in YAML(typ="safe").load((SYNC_CASE / "steps.yaml").read_text()):
        if "tick" in step:
            steps.append(("tick", step["tick"]))
        elif "block" in step:
            steps.append(("block", _case_file(step["block"])))
        elif "payload_status" in step:
            status = step["payload_status"]
            latest = status["latest_valid_hash"]
            steps.append(("payload", (status["status"], latest and bytes.fromhex(latest[2:]))))
        elif "checks" not in step:
            raise ValueError(f"no runner for the step {step}")
    return steps


def _signed(block: bytes) -> bytes:
    """A signed block in SSZ: the offset of the block, a zero signature, then the block."""
    return struct.pack("<I", 4 + 96) + bytes(96) + block


def _optimistic_node(
    steps: Sequence[consensus.ForkChoiceStep], roots: list[bytes], head: bytes
) -> bool:
    """Whether the node of the case is optimistic after the steps."""
    anchor_state, anchor_block = _case_file("anchor_state"), _case_file("anchor_block")
    return consensus.is_optimistic_node(
        "minimal", FORK, anchor_state, anchor_block, steps, roots, head, verify=False
    )


# A head root of the node; only its membership in the optimistic roots matters.
HEAD = bytes([1]) * 32


def test_optimistic_head_makes_an_optimistic_node():
    assert _optimistic_node([], [HEAD], HEAD) is True
    assert _optimistic_node(_case_steps(), [HEAD], HEAD) is True


def test_viable_branch_left():
    # After the case, the invalid blocks left the store and a valid branch remains.
    assert _optimistic_node(_case_steps(), [], ZERO) is False
    assert _optimistic_node([], [HEAD], ZERO) is False


def test_nothing_invalidated():
    # Without an invalid verdict, no block was dropped, so the second case cannot hold.
    steps = [step for step in _case_steps() if step[0] != "payload"]
    assert _optimistic_node(steps, [], ZERO) is False


def test_no_viable_branch_once_the_justified_block_is_invalid():
    # A verdict without a latest valid hash drops the anchor, which is the justified block.
    # Every descendant goes with it, so no branch is left.
    # No vector empties the tree while the justified block stays.
    # The theorem on the filtered tree covers that way.
    anchor = _signed(_case_file("anchor_block"))
    steps: list[consensus.ForkChoiceStep] = [
        *_case_steps(),
        ("payload", ("INVALID", None)),
        ("block", anchor),
    ]
    assert _optimistic_node(steps, [], ZERO) is True


_EXPORTS = [
    lambda fork, data: consensus.is_execution_block("mainnet", fork, data),
    lambda fork, data: consensus.is_optimistic_candidate_block("mainnet", fork, [data], 0, data),
    lambda fork, data: consensus.latest_verified_ancestor("mainnet", fork, [data], [], ZERO),
    lambda fork, data: consensus.on_valid_payload("mainnet", fork, [data], [], ZERO),
    lambda fork, data: consensus.on_invalidated_payload("mainnet", fork, [data], [], ZERO),
]
_IDS = ["execution", "candidate", "ancestor", "valid", "invalidated"]


@pytest.mark.parametrize("call", _EXPORTS, ids=_IDS)
@pytest.mark.parametrize("fork", ["phase0", "altair"])
def test_no_optimistic_sync_before_bellatrix(call, fork: str):
    with raises(ERROR, f"no optimistic sync at {fork}") as info:
        call(fork, G)
    assert info.value.code == 0


def test_no_latest_verified_ancestor_from_gloas():
    with raises(ERROR, "no optimistic sync at glamsterdam") as info:
        consensus.latest_verified_ancestor("minimal", GLOAS_FORK, GLOAS_BLOCKS, [], GG)
    assert info.value.code == 0


@pytest.mark.parametrize("fork", ["phase0", "altair", "glamsterdam"])
def test_no_optimistic_node_outside_bellatrix_to_fulu(fork: str):
    with raises(ERROR, f"no optimistic sync at {fork}") as info:
        consensus.is_optimistic_node("minimal", fork, b"", b"", [], [], ZERO)
    assert info.value.code == 0


def test_optimistic_node_head_of_another_length():
    anchor_state, anchor_block = _case_file("anchor_state"), _case_file("anchor_block")
    with raises(ERROR, "expected 32 bytes, got 31") as info:
        consensus.is_optimistic_node("minimal", FORK, anchor_state, anchor_block, [], [], bytes(31))
    assert info.value.code == 0


@pytest.mark.parametrize("call", _EXPORTS, ids=_IDS)
def test_block_that_does_not_decode(call):
    with raises(ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 84 0") as info:
        call(FORK, b"")
    assert info.value.code == 0


def test_roots_of_another_length():
    with raises(ERROR, "expected 32 bytes, got 31") as info:
        consensus.latest_verified_ancestor("mainnet", FORK, BLOCKS, [], bytes(31))
    assert info.value.code == 0
    with raises(ERROR, "expected 32 bytes, got 33") as info:
        consensus.on_valid_payload("mainnet", FORK, BLOCKS, [bytes(33)], RA)
    assert info.value.code == 0


def test_roots_must_be_bytes():
    with raises(TypeError, "cannot pass a value of type bytearray to Lean"):
        consensus.on_valid_payload("mainnet", FORK, BLOCKS, [bytearray(RA)], RA)  # ty: ignore[invalid-argument-type]
