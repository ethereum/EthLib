"""The bid and envelope of an honest builder from Gloas, on the payload of a fork choice case."""

from pathlib import Path

import pytest

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy
from raising import raises

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork_choice" / "minimal"

# The case holds a block of slot 1 and its payload, both valid.
CASE = "fork_choice/on_execution_payload_envelope/pyspec_tests/on_execution_payload_envelope_valid"

# The name of each fork in EthLib, by its name in the cases.
NAMES = {"gloas": "glamsterdam", "heze": "hegota"}

# The builder index of a proposer that builds its own payload.
SELF_BUILD = 2**64 - 1

# From Heze a bid has one bit for each of the 16 members of the inclusion list committee.
# No member of the case sent a list.
NO_BITS = {"gloas": None, "heze": bytes(2)}

# The builder index sits after four 32-byte fields, an address and the gas limit of a bid.
# The value sits after the builder index and the slot.
BUILDER_AT = 4 * 32 + 20 + 8
VALUE_AT = BUILDER_AT + 2 * 8

# A signed bid opens with the offset of the bid and the signature.
SIGNED_BID_HEAD = 4 + 96


def _read(fork: str, name: str) -> bytes:
    """The bytes of an SSZ file of the case, without the Snappy framing."""
    return snappy.decompress((FILES / fork / CASE / f"{name}.ssz_snappy").read_bytes())


def _file(fork: str, kind: str) -> str:
    """The name of the one file of a kind in the case, which ends with the root of its content."""
    (path,) = (FILES / fork / CASE).glob(f"{kind}_0x*.ssz_snappy")
    return path.name.removesuffix(".ssz_snappy")


def _offset(data: bytes, at: int) -> int:
    return int.from_bytes(data[at : at + 4], "little")


def signed_block(fork: str) -> bytes:
    return _read(fork, _file(fork, "block"))


def block(fork: str) -> bytes:
    """The block of slot 1, after the offset of the block and the signature of its proposer."""
    signed = signed_block(fork)
    return signed[_offset(signed, 0) :]


def envelope(fork: str) -> tuple[bytes, bytes, bytes]:
    """The envelope of the case, its payload and its requests."""
    signed = _read(fork, _file(fork, "execution_payload_envelope"))
    message = signed[_offset(signed, 0) :]
    # The envelope opens with the offsets of its payload and of its requests.
    payload = message[_offset(message, 0) : _offset(message, 4)]
    return message, payload, message[_offset(message, 4) :]


def builder_state(fork: str) -> bytes:
    """The state on which the payload of slot 1 was built: the anchor moved on to slot 1."""
    return consensus.process_slots("minimal", NAMES[fork], _read(fork, "anchor_state"), 1)


def fee_recipient(fork: str) -> bytes:
    """The fee recipient of the payload, after its parent hash."""
    _, payload, _ = envelope(fork)
    return payload[32:52]


def self_built(fork: str, bits: bytes | None = None) -> bytes:
    _, payload, requests = envelope(fork)
    return consensus.get_self_built_execution_payload_bid(
        "minimal",
        NAMES[fork],
        builder_state(fork),
        payload,
        requests,
        b"",
        fee_recipient(fork),
        bits,
    )


def bid(
    fork: str, builder_index: int, value: int, slot: int = 1, bits: bytes | None = None
) -> bytes:
    _, payload, requests = envelope(fork)
    return consensus.get_execution_payload_bid(
        "minimal",
        NAMES[fork],
        builder_state(fork),
        payload,
        requests,
        b"",
        slot,
        fee_recipient(fork),
        builder_index,
        value,
        bits,
    )


@pytest.mark.parametrize("fork", ["gloas", "heze"])
def test_envelope_of_the_case(fork: str):
    message, payload, requests = envelope(fork)
    built = consensus.get_execution_payload_envelope(
        "minimal", NAMES[fork], block(fork), payload, requests
    )
    assert built == message


@pytest.mark.parametrize("fork", ["gloas", "heze"])
def test_self_built_bid_of_the_case(fork: str):
    # The block of the case carries the self-built bid of its proposer.
    signed = self_built(fork, NO_BITS[fork])
    assert signed in signed_block(fork)
    # The signature is the signature at infinity.
    assert signed[4:SIGNED_BID_HEAD] == bytes([0xC0]) + bytes(95)


@pytest.mark.parametrize("fork", ["gloas", "heze"])
def test_bid_of_a_builder(fork: str):
    bits = NO_BITS[fork]
    message = self_built(fork, bits)[SIGNED_BID_HEAD:]
    assert bid(fork, SELF_BUILD, 0, bits=bits) == message
    built = bid(fork, 7, 1_000, bits=bits)
    assert built[:BUILDER_AT] == message[:BUILDER_AT]
    assert built[BUILDER_AT : BUILDER_AT + 8] == (7).to_bytes(8, "little")
    assert built[BUILDER_AT + 8 : VALUE_AT] == message[BUILDER_AT + 8 : VALUE_AT]
    assert built[VALUE_AT : VALUE_AT + 8] == (1_000).to_bytes(8, "little")
    assert built[VALUE_AT + 8 :] == message[VALUE_AT + 8 :]


def test_bid_for_another_slot():
    built = bid("gloas", SELF_BUILD, 0, 2)
    assert built[BUILDER_AT + 8 : VALUE_AT] == (2).to_bytes(8, "little")


@pytest.mark.parametrize("fork", ["bellatrix", "fusaka"])
def test_fork_without_a_bid(fork: str):
    with raises(SszError, f"no execution payload bid at {fork}") as info:
        consensus.get_execution_payload_bid(
            "minimal", fork, b"", b"", b"", b"", 1, bytes(20), SELF_BUILD, 0
        )
    assert info.value.code == 0
    with raises(SszError, f"no execution payload bid at {fork}") as info:
        consensus.get_self_built_execution_payload_bid(
            "minimal", fork, b"", b"", b"", b"", bytes(20)
        )
    assert info.value.code == 0


@pytest.mark.parametrize("fork", ["bellatrix", "fusaka"])
def test_fork_without_an_envelope(fork: str):
    with raises(SszError, f"no execution payload envelope at {fork}") as info:
        consensus.get_execution_payload_envelope("minimal", fork, b"", b"", b"")
    assert info.value.code == 0


def test_inclusion_list_bits_before_heze():
    with raises(SszError, "no inclusion list bits at glamsterdam") as info:
        self_built("gloas", bytes(2))
    assert info.value.code == 0
    with raises(SszError, "no inclusion list bits at glamsterdam") as info:
        bid("gloas", 7, 0, bits=bytes(2))
    assert info.value.code == 0


@pytest.mark.parametrize("bits", [None, b""], ids=["none", "empty"])
def test_inclusion_list_bits_missing_from_heze(bits: bytes | None):
    with raises(SszError, "inclusion list bits are required at hegota") as info:
        self_built("heze", bits)
    assert info.value.code == 0
    with raises(SszError, "inclusion list bits are required at hegota") as info:
        bid("heze", 7, 0, bits=bits)
    assert info.value.code == 0


def test_inclusion_list_bits_left_out_at_heze():
    _, payload, requests = envelope("heze")
    inputs = (builder_state("heze"), payload, requests, b"")
    with raises(SszError, "inclusion list bits are required at hegota") as info:
        consensus.get_self_built_execution_payload_bid(
            "minimal", "hegota", *inputs, fee_recipient("heze")
        )
    assert info.value.code == 0
    with raises(SszError, "inclusion list bits are required at hegota") as info:
        consensus.get_execution_payload_bid(
            "minimal", "hegota", *inputs, 1, fee_recipient("heze"), 7, 0
        )
    assert info.value.code == 0


def test_inclusion_list_bits_in_the_bid():
    # The bits are the last fixed field of the bid, and no blob commitment follows them.
    bits = bytes([0x01, 0x80])
    assert bid("heze", 7, 0, bits=bits).endswith(bits)
    assert self_built("heze", bits).endswith(bits)


# The bits of the 16 members take 2 bytes.
@pytest.mark.parametrize("size", [1, 3], ids=["short", "long"])
def test_inclusion_list_bits_of_the_wrong_length(size: int):
    message = f"input rejected: EthLib.Serialization.Ssz.Err.scope 2 {size}"
    with raises(SszError, message) as info:
        self_built("heze", bytes(size))
    assert info.value.code == 0
    with raises(SszError, message) as info:
        bid("heze", 7, 0, bits=bytes(size))
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("position", "data", "message"),
    [
        (0, b"", "scopeTooSmall 14405 0"),
        (1, b"", "scopeTooSmall 540 0"),
        (2, b"", "scopeTooSmall 20 0"),
        (3, bytes(47), "scopeUndivided 47 48"),
        (4, bytes(19), "scope 20 19"),
    ],
    ids=["state", "payload", "requests", "commitments", "fee recipient"],
)
def test_bid_input_that_does_not_decode(position: int, data: bytes, message: str):
    _, payload, requests = envelope("gloas")
    inputs = [builder_state("gloas"), payload, requests, b"", fee_recipient("gloas")]
    inputs[position] = data
    state, payload, requests, commitments, fee = inputs
    with raises(SszError, f"input rejected: EthLib.Serialization.Ssz.Err.{message}") as info:
        consensus.get_execution_payload_bid(
            "minimal", "glamsterdam", state, payload, requests, commitments, 1, fee, 7, 0
        )
    assert info.value.code == 0
    with raises(SszError, f"input rejected: EthLib.Serialization.Ssz.Err.{message}") as info:
        consensus.get_self_built_execution_payload_bid(
            "minimal", "glamsterdam", state, payload, requests, commitments, fee
        )
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("slot", "message"),
    [(-1, "can't convert negative int to unsigned"), (2**64, "int too big to convert")],
    ids=["negative", "above 64 bits"],
)
def test_slot_out_of_range(slot: int, message: str):
    with raises(OverflowError, message):
        bid("gloas", 7, 0, slot)


@pytest.mark.parametrize(
    ("position", "message"),
    [(0, "scopeTooSmall 84 0"), (1, "scopeTooSmall 540 0"), (2, "scopeTooSmall 20 0")],
    ids=["block", "payload", "requests"],
)
def test_envelope_input_that_does_not_decode(position: int, message: str):
    _, payload, requests = envelope("gloas")
    inputs = [block("gloas"), payload, requests]
    inputs[position] = b""
    with raises(SszError, f"input rejected: EthLib.Serialization.Ssz.Err.{message}") as info:
        consensus.get_execution_payload_envelope("minimal", "glamsterdam", *inputs)
    assert info.value.code == 0


def test_unknown_preset():
    with raises(SszError, "no preset is named nope") as info:
        consensus.get_execution_payload_envelope("nope", "glamsterdam", b"", b"", b"")
    assert info.value.code == 0
