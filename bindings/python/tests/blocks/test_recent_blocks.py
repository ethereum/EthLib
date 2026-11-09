"""The recent blocks of a chain, which Lean decodes for the state transition and newPayload."""

import pytest

from ethlib import engine
from ethlib.errors import BlockError, EngineError
from ethlib.execution import blocks
from ethlib.serialization import rlp
from raising import raises

# A chain at Frontier from block 0, with no account.
CONFIG = {
    "chainId": 1,
    "depositContractAddress": bytes(20),
    "activations": [["frontier", "block", 0]],
}
STATE = rlp.encode([])

# The fifteen fields of a Frontier header, from the parent hash to the nonce.
# Hashes and the Bloom filter are zero, the difficulty and the gas limit are 1, the rest is empty.
FIELDS = [bytes(32), bytes(32), bytes(20), bytes(32), bytes(32), bytes(32), bytes(256)]
HEADER = rlp.encode([*FIELDS, b"\x01", b"", b"\x01", b"", b"", b"", bytes(32), bytes(8)])

# A header that is one byte string, where a header is an RLP list of fields.
NOT_A_HEADER = rlp.encode(b"\x01")

HEADER_MESSAGE = "recent header rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList"
OMMER_MESSAGE = "recent ommers rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList"

# A recent block whose header does not decode, and one whose ommer does not decode.
BAD = [
    ([("frontier", NOT_A_HEADER, [])], HEADER_MESSAGE),
    ([("frontier", HEADER, [NOT_A_HEADER])], OMMER_MESSAGE),
]


@pytest.mark.parametrize("recent, message", BAD)
def test_state_transition(recent: list, message: str) -> None:
    with raises(BlockError, message) as error:
        blocks.state_transition(CONFIG, STATE, recent, "frontier", b"")
    assert error.value.code == 0


@pytest.mark.parametrize("recent, message", BAD)
def test_new_payload_on_chain(recent: list, message: str) -> None:
    with raises(EngineError, message) as error:
        engine.new_payload_on_chain(CONFIG, STATE, recent, "engine_newPayloadV1", [])
    assert error.value.code == 0
