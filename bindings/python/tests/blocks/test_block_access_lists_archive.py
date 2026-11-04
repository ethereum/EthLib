"""The vendored block access lists against the release archive of execution-specs."""

import json
from functools import cache
from pathlib import Path

import pytest

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

_FILE = Path(__file__).resolve().parents[4] / "tests" / "execution" / "blocks"
CASES = json.loads((_FILE / "block_access_lists.json").read_text())

pytestmark = pytest.mark.archive(ARCHIVE, *sorted({case["source"] for case in CASES}))


@cache
def _fixture(root: Path, source: str) -> dict:
    return json.loads((root / source).read_text())


def test_cases(archive) -> None:
    for case in CASES:
        payload = _fixture(archive, case["source"])[case["test"]]["engineNewPayloads"]
        params = payload[case["payload"]]["params"][0]
        # The list, the gas limit and the error are those of the release.
        assert case["bal"] == params["blockAccessList"].removeprefix("0x")
        assert case["gasLimit"] == int(params["gasLimit"], 16)
        assert case["error"] == payload[case["payload"]].get("validationError")
