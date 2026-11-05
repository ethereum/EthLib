"""The checks of engine_newPayload against every engine blockchain test of the release archive."""

import json
from collections import Counter

import pytest

from .cases import check

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

DIRECTORY = "fixtures/blockchain_tests_engine"

pytestmark = pytest.mark.archive(ARCHIVE, DIRECTORY)


def test_every_payload(archive) -> None:
    """Every payload from Paris to BPO2 gets the outcome that its fixture expects."""
    kinds = Counter()
    for path in sorted((archive / DIRECTORY).rglob("*.json")):
        for fixture in json.loads(path.read_text()).values():
            # Amsterdam is the next fork, with version 5 of the method.
            if "Amsterdam" in fixture["network"]:
                continue
            for payload in fixture["engineNewPayloads"]:
                method = f"engine_newPayloadV{payload['newPayloadVersion']}"
                kinds[check(fixture["network"], method, payload["params"],
                            payload.get("validationError"), payload.get("errorCode"))] += 1
    # Without the parent's state, a payload that fails only in execution is syncing.
    assert kinds == {"valid": 63256, "error": 46, "invalid": 51, "execution": 4991}
