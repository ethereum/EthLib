"""The Engine API methods against every engine blockchain test of the release archive."""

import json
from collections import Counter

import pytest

from ethlib import engine
from parity.runners import run_engine_chain

from .cases import check, config

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

DIRECTORY = "fixtures/blockchain_tests_engine"

pytestmark = pytest.mark.archive(ARCHIVE, DIRECTORY)

ZERO = "0x" + "00" * 32


def _fixtures(archive):
    """Every fixture from Paris to BPO2; Amsterdam, the next fork, has version 5 of the method."""
    for path in sorted((archive / DIRECTORY).rglob("*.json")):
        for fixture in json.loads(path.read_text()).values():
            if "Amsterdam" not in fixture["network"]:
                yield fixture


def test_every_payload(archive) -> None:
    """Every payload from Paris to BPO2 gets the outcome that its fixture expects."""
    kinds = Counter()
    for fixture in _fixtures(archive):
        for payload in fixture["engineNewPayloads"]:
            method = f"engine_newPayloadV{payload['newPayloadVersion']}"
            kinds[
                check(
                    fixture["network"],
                    method,
                    payload["params"],
                    payload.get("validationError"),
                    payload.get("errorCode"),
                )
            ] += 1
    # Without the parent's state, a payload that fails only in execution is syncing.
    assert kinds == {"valid": 63256, "error": 46, "invalid": 51, "execution": 4991}


def test_every_chain(archive) -> None:
    """On every chain, each valid payload becomes the head, and the last one is the last block."""
    chains = 0
    for fixture in _fixtures(archive):
        header = fixture["genesisBlockHeader"]
        genesis = header["hash"]
        chain_config = config(fixture["network"])
        # The genesis header writes 0 as `0x00`, which is no Engine API quantity.
        tree = [
            {
                "blockHash": genesis,
                "parentHash": ZERO,
                "valid": True,
                "number": hex(int(header["number"], 16)),
                "timestamp": hex(int(header["timestamp"], 16)),
            }
        ]
        head = genesis
        for payload in fixture["engineNewPayloads"]:
            if payload.get("validationError") or "errorCode" in payload:
                continue
            block = payload["params"][0]
            tree.append(
                {
                    "blockHash": block["blockHash"],
                    "parentHash": block["parentHash"],
                    "valid": True,
                    "number": block["blockNumber"],
                    "timestamp": block["timestamp"],
                }
            )
            state = {
                "headBlockHash": block["blockHash"],
                "safeBlockHash": genesis,
                "finalizedBlockHash": genesis,
            }
            method = f"engine_forkchoiceUpdatedV{payload['forkchoiceUpdatedVersion']}"
            response = engine.forkchoice_updated(chain_config, tree, method, [state, None])
            assert response["payloadStatus"]["status"] == "VALID"
            head = block["blockHash"]
        assert head == fixture["lastblockhash"]
        chains += 1
    assert chains == 56581


def test_every_payload_on_chain(archive) -> None:
    """With the parent's state, each payload is valid or invalid as its fixture expects."""
    kinds = Counter()
    for fixture in _fixtures(archive):
        kinds += run_engine_chain(fixture, fixture["pre"], fixture["genesisBlockHeader"])
    # The payloads that fail only in execution are now invalid, not syncing.
    assert kinds == {"valid": 63256, "error": 46, "invalid": 51, "execution": 4991}
