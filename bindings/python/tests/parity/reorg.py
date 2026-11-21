"""The runner of the reorg fixtures of execution-spec-tests, on the execution node of EthLib."""

import hashlib
import itertools
from dataclasses import dataclass, field
from typing import Any

import pytest

from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from ethlib.execution.blocks import RecentBlock

# The source leaves the transactions of a build to each node, and EthLib specifies no pool.
# So a fixture that sends a transaction to the pool does not run.
POOL = "EthLib specifies no transaction pool, so the builder of the node export takes none"

# The observations of the chain that the runner does not check, each with its reason.
UNCHECKED = {"assertTxStatus": POOL}

# The observations that the runner checks with JSON-RPC queries on the chain view of the node.
QUERIES = ("assertState", "assertReceipt", "assertLogs")

# The block tags of the JSON-RPC API; any other block of a step is a label.
TAGS = ("latest", "earliest", "safe", "finalized", "pending")

ZERO = "0x" + "00" * 32

# The version of `engine_newPayload` for a payload that a version of `engine_getPayload` returns.
# Version 5 of the request serves Osaka and the BPO forks, whose payloads take version 4.
NEW_PAYLOAD_VERSION = {1: 1, 2: 2, 3: 3, 4: 4, 5: 4, 6: 5}

# The version of `engine_forkchoiceUpdated` at the fork of a genesis block.
FORKCHOICE_VERSION = {
    "paris": 1,
    "shapella": 2,
    **dict.fromkeys(["dencun", "pectra", "fusaka", "bpo1", "bpo2", "bpo3", "bpo4", "bpo5"], 3),
    "glamsterdam": 4,
}

# The prefix of a blob versioned hash, by EIP-4844.
VERSIONED_HASH_VERSION_KZG = b"\x01"


def sends_transactions(steps: list[dict]) -> bool:
    """Whether a script, with its branches, sends a transaction to the pool."""
    return any(
        step["type"] == "sendRawTransaction"
        or any(sends_transactions(branch) for branch in step.get("branches", {}).values())
        for step in steps
    )


def _versioned_hash(commitment: str) -> str:
    """The versioned hash of a KZG commitment: its SHA-256 hash with the first byte replaced."""
    digest = hashlib.sha256(bytes.fromhex(commitment.removeprefix("0x"))).digest()
    return "0x" + (VERSIONED_HASH_VERSION_KZG + digest[1:]).hex()


def _request(method: str, params: list[Any]) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}


@dataclass
class ReorgScript:
    """The script of one fixture on one node: the requests sent so far, and the block labels."""

    fixture: dict[str, Any]
    config: dict[str, Any]
    state: bytes
    anchor: RecentBlock
    # The block hash of each label, and the parent hash and the number of each block hash.
    hashes: dict[str, str] = field(init=False, default_factory=dict)
    parents: dict[str, str] = field(init=False, default_factory=dict)
    numbers: dict[str, int] = field(init=False, default_factory=dict)
    # The `engine_newPayload` request of each label.
    payloads: dict[str, dict[str, Any]] = field(init=False, default_factory=dict)
    # The requests sent, and the answers of the last run, which may run requests ahead.
    sent: list[dict[str, Any]] = field(init=False, default_factory=list)
    answers: list[tuple[dict[str, Any], dict[str, Any]]] = field(init=False, default_factory=list)
    # The forkchoice state after the last request, and the attributes of each payload ID.
    forkchoice: dict[str, str] = field(init=False, default_factory=dict)
    attributes: dict[str, dict[str, Any]] = field(init=False, default_factory=dict)
    payload_id: str | None = field(init=False, default=None)

    def __post_init__(self) -> None:
        genesis = "0x" + keccak256(self.anchor[1]).hex()
        self.hashes |= {"genesis": genesis, "zero": ZERO}
        self.numbers[genesis] = 0
        self.forkchoice = {"headBlockHash": genesis}
        for label, block in self.fixture["blocks"].items():
            payload = block["payload"]
            self._label(label, block["parent"], payload["params"][0])
            self.payloads[label] = _request(
                f"engine_newPayloadV{payload['newPayloadVersion']}", payload["params"]
            )

    def _label(self, label: str, parent: str, payload: dict[str, Any]) -> None:
        block = payload["blockHash"]
        self.hashes[label] = block
        self.parents[block] = self.hashes[parent]
        self.numbers[block] = int(payload["blockNumber"], 16)

    def start(self) -> None:
        """Make the genesis block the head, as the consumer does before the steps."""
        version = FORKCHOICE_VERSION[self.anchor[0]]
        request = self._forkchoice_request({"head": "genesis", "version": version})
        answer = self._call(request, [])
        assert answer["result"]["payloadStatus"]["status"] == "VALID", answer

    def _call(self, request: dict[str, Any], ahead: list[dict[str, Any]]) -> dict[str, Any]:
        """The answer to a request after those sent, running the requests `ahead` too if needed."""
        index = len(self.sent)
        self.sent.append(request)
        # The node answers each request from those before it alone, so a run ahead stays valid.
        # A request ahead that the export refuses would fail the run, so the run is then redone.
        if index >= len(self.answers) or self.answers[index][0] != request:
            try:
                results = self._run(self.sent + ahead)
            except engine.EngineError:
                if not ahead:
                    raise
                results = self._run(self.sent)
            self.answers = results
        _, out = self.answers[index]
        self.forkchoice = out["forkchoice"]
        return out["response"]

    def _run(self, requests: list[dict[str, Any]]) -> list[tuple[dict[str, Any], dict[str, Any]]]:
        results = engine.run_node(self.config, self.state, self.anchor, requests)
        return list(zip(requests, results, strict=True))

    def _forkchoice_request(self, step: dict[str, Any]) -> dict[str, Any]:
        state = {
            "headBlockHash": self.hashes[step["head"]],
            "safeBlockHash": self.hashes[step.get("safe", "zero")],
            "finalizedBlockHash": self.hashes[step.get("finalized", "zero")],
        }
        return _request(
            f"engine_forkchoiceUpdatedV{step['version']}", [state, step.get("payloadAttributes")]
        )

    def _ahead(self, steps: list[dict[str, Any]]) -> list[dict[str, Any]]:
        """The requests of the next steps, up to the first one that needs an answer first."""
        requests = []
        for step in steps:
            if step["type"] == "forkchoiceUpdated":
                labels = (step["head"], step.get("safe", "zero"), step.get("finalized", "zero"))
                if not all(label in self.hashes for label in labels):
                    break
                requests.append(self._forkchoice_request(step))
            elif step["type"] == "newPayload" and step["block"] in self.payloads:
                requests.append(self.payloads[step["block"]])
            elif step["type"] in ("newPayload", "getPayload", *QUERIES):
                break
        return requests

    def run(self, steps: list[dict[str, Any]]) -> None:
        """Run steps in order, each Engine API step followed by the branch of its outcome."""
        for i, step in enumerate(steps):
            kind = step["type"]
            if kind == "newPayload":
                request = self.payloads[step["block"]]
            elif kind == "forkchoiceUpdated":
                request = self._forkchoice_request(step)
            elif kind == "getPayload":
                self._get_payload(step)
                continue
            elif kind == "assertHead":
                self._assert_head(step)
                continue
            elif kind == "assertCanonical":
                self._assert_canonical(step)
                continue
            elif kind == "assertState":
                self._assert_state(step)
                continue
            elif kind == "assertReceipt":
                self._assert_receipt(step)
                continue
            elif kind == "assertLogs":
                self._assert_logs(step)
                continue
            else:
                assert kind in UNCHECKED, kind
                continue
            answer = self._call(request, self._ahead(steps[i + 1 :]))
            if kind == "forkchoiceUpdated" and "result" in answer:
                self._remember_build(step, answer["result"])
            outcome = next((o for o in step["expect"] if self._matches(step, o, answer)), None)
            assert outcome is not None, (step, answer)
            self.run(step.get("branches", {}).get(outcome["id"], []))

    def _remember_build(self, step: dict[str, Any], result: dict[str, Any]) -> None:
        # A request for a payload reads the ID of the last update that did not fail.
        self.payload_id = result["payloadId"]
        if self.payload_id is not None:
            self.attributes[self.payload_id] = step["payloadAttributes"]

    def _matches(
        self, step: dict[str, Any], outcome: dict[str, Any], answer: dict[str, Any]
    ) -> bool:
        """Whether an answer meets every field that an outcome sets."""
        error = answer.get("error")
        if "errorCode" in outcome:
            return error is not None and int(error["code"]) == int(outcome["errorCode"])
        if outcome.get("anyError"):
            return error is not None
        if error is not None:
            return False
        result = answer["result"]
        status = result["payloadStatus"] if step["type"] == "forkchoiceUpdated" else result
        checks = [
            "status" not in outcome or status["status"] == outcome["status"],
            self._latest_valid(outcome.get("latestValidHash", "any"), status["latestValidHash"]),
            outcome.get("validationError") != "required" or status.get("validationError"),
            outcome.get("validationError") != "none" or not status.get("validationError"),
            outcome.get("payloadId") != "nonNull" or result.get("payloadId") is not None,
            outcome.get("payloadId") != "null" or result.get("payloadId") is None,
            "headMoved" not in outcome
            or (self.forkchoice["headBlockHash"] == self.hashes[step["head"]])
            == outcome["headMoved"],
        ]
        return all(checks)

    def _latest_valid(self, expected: str, got: str | None) -> bool:
        if expected == "any":
            return True
        if expected == "null":
            return got is None
        return got == self.hashes[expected]

    def _get_payload(self, step: dict[str, Any]) -> None:
        """Read the build of the last payload ID, check it, and bind its label."""
        version = int(step["version"])
        assert self.payload_id is not None, step
        answer = self._call(_request(f"engine_getPayloadV{version}", [self.payload_id]), [])
        assert "result" in answer, (step, answer)
        result = answer["result"] if version > 1 else {"executionPayload": answer["result"]}
        payload = result["executionPayload"]
        assert payload["parentHash"] == self.hashes[step["parent"]], (step, payload)
        transactions = payload["transactions"]
        for ref in step.get("transactionsInclude", []):
            assert self._transaction(ref) in transactions, (step, ref)
        for ref in step.get("transactionsExclude", []):
            assert self._transaction(ref) not in transactions, (step, ref)
        params: list[Any] = [payload]
        new_version = NEW_PAYLOAD_VERSION[version]
        if new_version >= 3:
            # The builder of the export takes no transaction, so the bundle is empty today.
            commitments = result["blobsBundle"]["commitments"]
            root = self.attributes[self.payload_id]["parentBeaconBlockRoot"]
            params += [[_versioned_hash(c) for c in commitments], root]
        if new_version >= 4:
            params.append(result["executionRequests"])
        self._label(step["bind"], step["parent"], payload)
        self.payloads[step["bind"]] = _request(f"engine_newPayloadV{new_version}", params)

    def _transaction(self, ref: dict[str, Any]) -> str:
        params = self.payloads[ref["block"]]["params"]
        return params[0]["transactions"][int(ref.get("index", 0))]

    def _assert_head(self, step: dict[str, Any]) -> None:
        for name, key in (
            ("latest", "headBlockHash"),
            ("safe", "safeBlockHash"),
            ("finalized", "finalizedBlockHash"),
        ):
            if name in step:
                assert self.forkchoice[key] == self.hashes[step[name]], (step, self.forkchoice)

    def _assert_canonical(self, step: dict[str, Any]) -> None:
        # The canonical chain is the chain of the head, by the parents of the blocks.
        chain: dict[int, str] = {}
        block = self.forkchoice["headBlockHash"]
        while True:
            chain[self.numbers[block]] = block
            if block == self.hashes["genesis"]:
                break
            block = self.parents[block]
        for height, expected in step["blocks"].items():
            want = None if expected is None else self.hashes[expected]
            assert chain.get(int(height, 16)) == want, (step, chain)

    def _query(self, method: str, params: list[Any]) -> Any:
        """The result of a JSON-RPC query on the chain view of the node after the requests sent."""
        answer = self._call(_request(method, params), [])
        assert "result" in answer, (method, params, answer)
        return answer["result"]

    def _block(self, at: str) -> str:
        return at if at in TAGS else self.hashes[at]

    def _assert_state(self, step: dict[str, Any]) -> None:
        at = self._block(step["at"])
        for address, account in step["accounts"].items():
            queries = [
                ("balance", "eth_getBalance", [address, at]),
                ("nonce", "eth_getTransactionCount", [address, at]),
            ]
            for name, method, params in queries:
                if name in account:
                    got = int(self._query(method, params), 16)
                    assert got == int(account[name], 16), (step, address, name, got)
            if "code" in account:
                got = self._query("eth_getCode", [address, at])
                assert got == account["code"], (step, address, got)
            for slot, value in account.get("storage", {}).items():
                got = int(self._query("eth_getStorageAt", [address, slot, at]), 16)
                assert got == int(value, 16), (step, address, slot, got)

    def _assert_receipt(self, step: dict[str, Any]) -> None:
        # The receipt names the block of the step, or there is none on the canonical chain.
        raw = bytes.fromhex(self._transaction(step["tx"]).removeprefix("0x"))
        receipt = self._query("eth_getTransactionReceipt", ["0x" + keccak256(raw).hex()])
        got = None if receipt is None else receipt["blockHash"]
        want = self.hashes[step["block"]] if "block" in step else None
        assert got == want, (step, receipt)

    def _assert_logs(self, step: dict[str, Any]) -> None:
        # The logs of the address come from the listed blocks, in order.
        query = {
            "address": step["address"],
            "fromBlock": self._block(step["fromBlock"]),
            "toBlock": self._block(step["toBlock"]),
        }
        logs = self._query("eth_getLogs", [query])
        assert all(log["address"] == step["address"].lower() for log in logs), (step, logs)
        got = [block for block, _ in itertools.groupby(log["blockHash"] for log in logs)]
        assert got == [self.hashes[label] for label in step["blocks"]], (step, logs)


def run(fixture: dict[str, Any], config: dict[str, Any], state: bytes, anchor: RecentBlock) -> None:
    """Run the script of a fixture on a node that starts from its genesis block."""
    # `minReorgDepth` bounds the reorganizations of client software, and the node has no bound.
    if sends_transactions(fixture["steps"]):
        pytest.skip(POOL)
    script = ReorgScript(fixture, config, state, anchor)
    script.start()
    script.run(fixture["steps"])
