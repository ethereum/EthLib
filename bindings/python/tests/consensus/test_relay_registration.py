"""The answer of a relay to a request for the registration of a key."""

import json
import struct
from pathlib import Path

from ethlib import consensus

EXAMPLES = Path(__file__).resolve().parents[4] / "tests/consensus/builder_api"

# The registration example of the Builder API: its message, then its signature.
# The message holds the fee recipient, the gas limit, the timestamp, then the key at bytes 36 to 84.
EXAMPLE = (EXAMPLES / "bellatrix" / "signed_validator_registrations.ssz").read_bytes()
EXAMPLE_JSON = json.loads(
    (EXAMPLES / "bellatrix" / "signed_validator_registrations.json").read_text()
)["value"][0]
PUBKEY = "0x" + EXAMPLE[36:84].hex()


def _at(timestamp: int) -> bytes:
    """The example registration at another timestamp."""
    return EXAMPLE[:28] + struct.pack("<Q", timestamp) + EXAMPLE[36:]


def test_latest_registration() -> None:
    """A key registered at times 100 and 200 gets 200 with the registration of time 200."""
    status, body = consensus.relay_validator_registration([_at(100), _at(200)], PUBKEY)
    assert status == 200
    assert body["message"]["timestamp"] == "200"
    assert body["message"]["pubkey"] == EXAMPLE_JSON["message"]["pubkey"]
    assert body["signature"] == EXAMPLE_JSON["signature"]


def test_example_registration() -> None:
    """The answer for the example's key is the JSON of the example."""
    assert consensus.relay_validator_registration([EXAMPLE], PUBKEY) == (200, EXAMPLE_JSON)


def test_missing_pubkey() -> None:
    """A request without a key gets 400, with the message of the source's example."""
    assert consensus.relay_validator_registration([EXAMPLE], None) == (
        400,
        {"code": 400, "message": "missing pubkey argument"},
    )


def test_malformed_pubkey() -> None:
    """A key that is not 48 bytes of hex gets 400."""
    assert consensus.relay_validator_registration([EXAMPLE], PUBKEY[:-2]) == (
        400,
        {"code": 400, "message": "invalid pubkey argument"},
    )


def test_unknown_key() -> None:
    """A key that never registered has no answer in the source."""
    assert consensus.relay_validator_registration([EXAMPLE], "0x" + "11" * 48) is None
