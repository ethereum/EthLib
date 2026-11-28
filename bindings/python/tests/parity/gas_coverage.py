"""Report the gas rules exercised by pinned execution fixtures."""

import argparse
import json
import os
import selectors
import subprocess
from collections import Counter
from collections.abc import Callable, Generator, Iterable, Mapping, Set
from concurrent.futures import ProcessPoolExecutor
from contextlib import contextmanager
from dataclasses import dataclass, field
from multiprocessing import get_context
from pathlib import Path, PurePosixPath
from time import monotonic

import pytest

import archives

from . import catalogue, harness, legacy, runners
from .catalogue import Case

HEZE = "tests-heze-devnet"
HEZE_TRANSITIONS = {"BPO2ToBPO3AtTime15k", "BPO3ToBPO4AtTime15k"}
LEGACY = "legacytests"
DAO = "HomesteadToDaoAt5"
LEGACY_FORMAT = "legacy_blockchain"
SOURCES = {
    "execution-spec-tests": catalogue.EXECUTION,
    LEGACY: catalogue.LEGACY,
    **catalogue.DEVNETS,
}
DEFAULT_SUITES = ("execution-spec-tests", LEGACY, HEZE)
VENDORED_LEGACY = archives.REPO / "tests" / "execution" / "legacytests"
# The release leaves these early CREATE and SSTORE gas rules unobserved.
LEGACY_GAS_CASES = {
    "Constantinople/BlockchainTests/GeneralStateTests/stInitCodeTest/"
    "CallContractToCreateContractNoCash_d0g0v0.json": (
        "CallContractToCreateContractNoCash_d0g0v0",
        ("Frontier", "Homestead", "EIP150"),
    ),
    "Cancun/BlockchainTests/GeneralStateTests/stSStoreTest/"
    "SstoreCallToSelfSubRefundBelowZero.json": (
        "SstoreCallToSelfSubRefundBelowZero_d0g0v0",
        ("Istanbul",),
    ),
}
EXECUTABLE = archives.REPO / ".lake/build/bin/gas-coverage"
BRIDGE_TIMEOUT = 120
BRIDGE_EXIT_TIMEOUT = 5
MAX_JOBS = 16
EXECUTION_NETWORK_RANK = {
    name: rank for rank, name in enumerate(catalogue.EXECUTION_FORKS + catalogue.BOGOTA_NETWORKS)
}
LEGACY_NETWORK_RANK = {name: rank for rank, name in enumerate(catalogue.LEGACY_FORKS)}
Request = Callable[[dict], dict]
Outcome = tuple[str, str, str, str, str]


class FixtureError(ValueError):
    """The interpreter rejected a transaction or block."""


@dataclass
class Bridge:
    """One request and response per line of the coverage subprocess."""

    stdin: int
    stdout: int
    timeout: float

    def request(self, payload: dict) -> dict:
        """Exchange one line within a single deadline for writing and reading."""
        request = f"{payload['kind']} request for {payload['fork']}"
        data = memoryview((json.dumps(payload, separators=(",", ":")) + "\n").encode())
        deadline = monotonic() + self.timeout
        with selectors.DefaultSelector() as ready:
            ready.register(self.stdin, selectors.EVENT_WRITE)
            while data:
                wait_for_pipe(ready, deadline, f"sending the {request}")
                try:
                    written = os.write(self.stdin, data)
                except BlockingIOError:
                    continue
                except BrokenPipeError as error:
                    raise RuntimeError(
                        f"gas-coverage closed its input during the {request}"
                    ) from error
                data = data[written:]
            ready.unregister(self.stdin)
            ready.register(self.stdout, selectors.EVENT_READ)
            line = bytearray()
            while True:
                wait_for_pipe(ready, deadline, f"waiting for the {request}")
                try:
                    chunk = os.read(self.stdout, 64 * 1024)
                except BlockingIOError:
                    continue
                if not chunk:
                    raise RuntimeError(f"gas-coverage stopped before replying to the {request}")
                head, newline, tail = chunk.partition(b"\n")
                line.extend(head)
                if newline:
                    if tail:
                        raise RuntimeError(f"gas-coverage sent extra data after the {request}")
                    break
        return decode_reply(line, payload["kind"], request)


def wait_for_pipe(selector: selectors.BaseSelector, deadline: float, action: str) -> None:
    """Wait for a pipe to be ready until the request deadline."""
    remaining = deadline - monotonic()
    if remaining <= 0 or not selector.select(remaining):
        raise RuntimeError(f"gas-coverage timed out while {action}")


def decode_reply(line: bytes | bytearray, kind: str, request: str) -> dict:
    """Read the reply envelope and distinguish protocol errors from fixture rejections."""
    try:
        result = json.loads(line)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"gas-coverage returned invalid JSON for the {request}") from error
    if not isinstance(result, dict):
        raise RuntimeError(f"gas-coverage returned a non-object reply to the {request}")
    if "error" in result:
        rejection = result["error"]
        if (
            len(result) != 1
            or not isinstance(rejection, dict)
            or type(code := rejection.get("code")) is not int
            or not 0 <= code < 2**32
            or not isinstance(message := rejection.get("message"), str)
            or not message
        ):
            raise RuntimeError(f"gas-coverage returned an invalid error for the {request}")
        if kind == "inventory":
            raise RuntimeError(f"gas-coverage rejected the {request}: {message}")
        raise FixtureError(message)
    return result


@contextmanager
def open_bridge(
    executable: Path, *, timeout: float = BRIDGE_TIMEOUT, exit_timeout: float = BRIDGE_EXIT_TIMEOUT
) -> Generator[Bridge, None, None]:
    """Start a bridge and reap the child even when replay fails or times out."""
    process = subprocess.Popen(
        [str(executable)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, bufsize=0
    )
    assert process.stdin is not None and process.stdout is not None
    try:
        stdin, stdout = process.stdin.fileno(), process.stdout.fileno()
        os.set_blocking(stdin, False)
        os.set_blocking(stdout, False)
        yield Bridge(stdin, stdout, timeout)
        process.stdin.close()
        try:
            status = process.wait(timeout=exit_timeout)
        except subprocess.TimeoutExpired as error:
            raise RuntimeError("gas-coverage did not exit after closing its input") from error
        if status:
            raise RuntimeError("gas-coverage exited with an error")
    except BaseException:
        process.kill()
        try:
            process.wait(timeout=exit_timeout)
        except subprocess.TimeoutExpired as error:
            raise RuntimeError("gas-coverage did not exit after being killed") from error
        raise
    finally:
        process.stdin.close()
        process.stdout.close()


@dataclass
class Counts:
    """The gas events and validated executions at one active fork."""

    gas_rules: Counter[str] = field(default_factory=Counter)
    state_transactions: int = 0
    blocks: int = 0

    def merge(self, other: "Counts") -> None:
        """Add another batch of results at the same fork."""
        self.gas_rules.update(other.gas_rules)
        self.state_transactions += other.state_transactions
        self.blocks += other.blocks


@dataclass
class Report:
    """The fixture outcomes, coverage by active fork, and failure details."""

    outcomes: Counter[Outcome] = field(default_factory=Counter)
    counts: dict[str, Counts] = field(default_factory=dict)
    failures: list[tuple[Case, str]] = field(default_factory=list)

    def outcome(self, case: Case, status: str, reason: str = "") -> None:
        """Record one fixture outcome under its suite, network and format."""
        self.outcomes[case.suite, case.fork, case.group, status, reason] += 1

    def merge(self, other: "Report") -> None:
        """Combine the outcomes, failures and fork counts from another worker."""
        self.outcomes.update(other.outcomes)
        self.failures.extend(other.failures)
        for fork, counts in other.counts.items():
            self.counts.setdefault(fork, Counts()).merge(counts)


def select_cases(
    cases: Iterable[Case],
    networks: Set[str],
    formats: Set[str],
    group: PurePosixPath | None,
) -> list[Case]:
    """Select fixtures by index metadata and group them by file for replay."""
    return sorted(
        harness.select_cases(cases, group, networks=networks or None, formats=formats or None),
        key=lambda case: (case.path, case.id, case.fork),
    )


def heze_supplement_matches(
    networks: Set[str], formats: Set[str], group: PurePosixPath | None
) -> bool:
    """Whether the filters can select a block in the default Heze supplement."""
    directories = [
        PurePosixPath("fixtures/blockchain_tests") / f"for_{network.lower()}"
        for network in HEZE_TRANSITIONS
    ]
    return (
        (not networks or bool(networks & HEZE_TRANSITIONS))
        and (not formats or "blockchain_test" in formats)
        and (
            group is None
            or any(path.is_relative_to(group) or group.is_relative_to(path) for path in directories)
        )
    )


def source_matches(
    suite: str, networks: Set[str], formats: Set[str], group: PurePosixPath | None
) -> bool:
    """Rule out sources whose formats, networks or layout do not match the filters."""
    fixtures = PurePosixPath("fixtures")
    if suite == LEGACY:
        return (not formats or LEGACY_FORMAT in formats) and (
            group is None or not group.is_relative_to(fixtures)
        )
    if (formats and formats <= {LEGACY_FORMAT}) or (networks and networks <= {DAO, "EIP150"}):
        return False
    return group is None or group.is_relative_to(fixtures) or fixtures.is_relative_to(group)


def source_cases(suite: str, archive: str, heze_supplement: bool = False) -> Iterable[Case]:
    """List a source's cases, including unsupported execution fixtures for the report."""
    if suite == LEGACY:
        yield from (
            case
            for case in catalogue.legacy_cases(VENDORED_LEGACY)
            if case.fork == DAO and case.group == LEGACY_FORMAT
        )
        for path, (name, networks) in LEGACY_GAS_CASES.items():
            for network in networks:
                yield Case(suite, "", network, LEGACY_FORMAT, f"{path}::{name}_{network}", path)
        return
    for entry in catalogue.execution_index(archive):
        if (
            suite == HEZE
            and heze_supplement
            and (entry["format"] != "blockchain_test" or entry["fork"] not in HEZE_TRANSITIONS)
        ):
            continue
        yield Case(
            suite, "", entry["fork"], entry["format"], entry["id"], "fixtures/" + entry["json_path"]
        )


def skip_reason(case: Case, disagreements: Mapping[tuple[str, str | None], dict]) -> str:
    """Explain why the report skips a fixture, or return an empty string for replay."""
    if harness.disagreement(case, disagreements) is not None:
        return "listed parity disagreement"
    if case.suite != LEGACY and case.fork not in EXECUTION_NETWORK_RANK:
        return "fixture network is outside the implemented execution forks"
    if reason := catalogue.EXCLUDED_FORMATS.get(case.group):
        return reason
    # Parity has no plan for these networks, and must keep failing loudly on them.
    unplanned_bogota = (
        case.fork in catalogue.BOGOTA_NETWORKS and case.suite not in catalogue.DEVNETS
    )
    unknown_state_network = (
        case.group in ("state_test", "transaction_test")
        and case.fork not in runners.FORK_OF_NETWORK
    )
    if unplanned_bogota or unknown_state_network:
        return "no parity runner for this fixture at this network"
    if runners.runner(case) is None:
        return runners.plan(case) or "no parity runner for this fixture at this network"
    if case.group not in REPLAYERS:
        return "the coverage runner does not replay this fixture format"
    return ""


def replay_state(root: Path, case: Case, request: Request) -> dict[str, Counts]:
    """Credit a state test after its observed output agrees with its fixture."""
    (fork, chain_id, tx, pre, env), post = runners.state_test_input(root, case)
    expected = post.get("expectException")
    try:
        response = parse_state_reply(
            request(
                {
                    "kind": "state",
                    "fork": fork,
                    "chainId": chain_id,
                    "tx": tx.hex(),
                    "state": pre.hex(),
                    "env": env.hex(),
                }
            )
        )
    except FixtureError as error:
        if expected is None:
            raise
        assert any(runners.names_in_block(name, str(error)) for name in expected.split("|")), (
            expected,
            str(error),
        )
        return {fork: Counts()}
    if expected is not None:
        raise AssertionError(f"transaction accepted despite expected exception {expected}")
    assert response.root == bytes.fromhex(post["hash"][2:]), "state root differs"
    runners.check_state_test_receipt(
        post, response.logs_hash, response.gas_used, response.succeeded
    )
    if pinned := post.get("receipt", {}).get("rlp"):
        assert response.receipt == bytes.fromhex(pinned[2:]), "receipt bytes differ"
    return {fork: Counts(gas_rules=response.gas_rules, state_transactions=1)}


def gas_events(response: dict) -> Counter[str]:
    """Validate the positive count of each observed rule."""
    counts = response.get("gasRules")
    if not isinstance(counts, dict) or any(
        not isinstance(rule, str) or not rule or type(count) is not int or count <= 0
        for rule, count in counts.items()
    ):
        raise RuntimeError("gas-coverage returned invalid gas event counts")
    return Counter(counts)


@dataclass(frozen=True)
class InventoryReply:
    """Which rules the runner can observe at one fork in activation order."""

    fork_index: int
    rules: frozenset[str]


def parse_inventory_reply(response: dict, fork: str) -> InventoryReply:
    """Validate the fork index and the distinct rule names in its inventory."""
    rank = response.get("forkIndex")
    if type(rank) is not int or rank < 0:
        raise RuntimeError(f"invalid fork index in the {fork} inventory")
    rules = response.get("gasRules")
    if not isinstance(rules, list) or not all(isinstance(rule, str) and rule for rule in rules):
        raise RuntimeError(f"invalid gas rule inventory for {fork}")
    names = frozenset(rules)
    if len(names) != len(rules):
        raise RuntimeError(f"duplicate gas rules in the {fork} inventory")
    return InventoryReply(rank, names)


@dataclass(frozen=True)
class StateReply:
    """The gas events and fixture evidence of an observed state test."""

    gas_rules: Counter[str]
    root: bytes
    logs_hash: bytes
    gas_used: int
    succeeded: bool
    receipt: bytes


def reply_hex(value: object, field: str, size: int | None = None) -> bytes:
    """Decode a nonempty reply value in hexadecimal, with an optional fixed byte count."""
    message = f"gas-coverage returned invalid {field}"
    if not isinstance(value, str) or not value:
        raise RuntimeError(message)
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise RuntimeError(message) from error
    if len(decoded) * 2 != len(value) or (size is not None and len(decoded) != size):
        raise RuntimeError(message)
    return decoded


def parse_state_reply(response: dict) -> StateReply:
    """Validate every field of a state-test reply before it reaches fixture checks."""
    gas_used = response.get("gasUsed")
    if type(gas_used) is not int or gas_used < 0:
        raise RuntimeError("gas-coverage returned invalid gasUsed")
    succeeded = response.get("succeeded")
    if type(succeeded) is not bool:
        raise RuntimeError("gas-coverage returned invalid succeeded")
    return StateReply(
        gas_events(response),
        reply_hex(response.get("stateRoot"), "stateRoot", 32),
        reply_hex(response.get("logsHash"), "logsHash", 32),
        gas_used,
        succeeded,
        reply_hex(response.get("receipt"), "receipt"),
    )


@dataclass(frozen=True)
class BlockReply:
    """The gas events, state and encoded receipts of an observed block."""

    gas_rules: Counter[str]
    state: bytes
    receipts: list[bytes]


def parse_block_reply(response: dict) -> BlockReply:
    """Validate and decode the state and receipts returned for a block."""
    receipts = response.get("receipts")
    if not isinstance(receipts, list):
        raise RuntimeError("gas-coverage returned invalid receipts")
    return BlockReply(
        gas_events(response),
        reply_hex(response.get("state"), "state"),
        [reply_hex(receipt, f"receipt {index}") for index, receipt in enumerate(receipts)],
    )


def replay_blockchain(root: Path, case: Case, request: Request) -> dict[str, Counts]:
    """Credit each accepted block to the fork at which the fixture runs it."""
    by_fork: dict[str, Counts] = {}

    def transition(
        config: dict,
        state: bytes,
        recent: legacy.RecentBlocks,
        fork: str,
        raw: bytes,
        seal: bool,
        receipts: list[dict] | None = None,
    ) -> bytes:
        if isinstance(address := config.get("depositContractAddress"), bytes):
            config = {**config, "depositContractAddress": "0x" + address.hex()}
        response = parse_block_reply(
            request(
                {
                    "kind": "block",
                    "fork": fork,
                    "config": config,
                    "state": state.hex(),
                    "recent": [
                        [name, header.hex(), [ommer.hex() for ommer in ommers]]
                        for name, header, ommers in recent
                    ],
                    "block": raw.hex(),
                    "checkSeal": seal,
                }
            )
        )
        if receipts is not None:
            assert len(response.receipts) == len(receipts), "block receipt count differs"
            for index, (receipt, encoded) in enumerate(
                zip(receipts, response.receipts, strict=True)
            ):
                if "rlp" in receipt:
                    assert encoded == bytes.fromhex(receipt["rlp"][2:]), (
                        f"block receipt {index} bytes differ"
                    )
        counts = by_fork.setdefault(fork, Counts())
        counts.gas_rules.update(response.gas_rules)
        counts.blocks += 1
        return response.state

    if case.group == LEGACY_FORMAT:
        legacy.run_blockchain(root, case, transition=transition)
        forks = catalogue.LEGACY_FORKS[case.fork]
        if not by_fork and len(forks) == 1:
            return {forks[0]: Counts()}
    else:
        runners.check_blockchain_test(root, case, transition)
        if not by_fork and (fork := runners.static_fork(case.fork)) is not None:
            return {fork: Counts()}
    return by_fork


# The formats that the observer can run, with their replay functions.
REPLAYERS = {
    "state_test": replay_state,
    "blockchain_test": replay_blockchain,
    LEGACY_FORMAT: replay_blockchain,
}


def replay_cases(root: Path, cases: list[Case], request: Request) -> Report:
    """Accumulate coverage only from fixtures that pass all their checks."""
    report = Report()
    for case in cases:
        replay = REPLAYERS[case.group]
        try:
            by_fork = replay(root, case, request)
        except (AssertionError, FixtureError, pytest.fail.Exception) as error:
            report.failures.append((case, str(error) or "fixture result differs"))
            report.outcome(case, "failed", "parity check failed")
            continue
        for fork, counts in by_fork.items():
            report.counts.setdefault(fork, Counts()).merge(counts)
        observed = any(counts.gas_rules for counts in by_fork.values())
        report.outcome(case, "traced" if observed else "checked without observed events")
    return report


def replay_batch(root: Path, cases: list[Case], executable: Path) -> Report:
    """Replay one batch through a single coverage runner process."""
    with open_bridge(executable) as bridge:
        return replay_cases(root, cases, bridge.request)


def partition_cases(cases: list[Case], jobs: int) -> list[list[Case]]:
    """Balance workers by case count while keeping each fixture file in one worker."""
    by_path: dict[str, list[Case]] = {}
    for case in cases:
        by_path.setdefault(case.path, []).append(case)
    batches: list[list[Case]] = [[] for _ in range(min(jobs, len(by_path)))]
    for group in sorted(by_path.values(), key=len, reverse=True):
        min(batches, key=len).extend(group)
    return batches


def replay_source(
    report: Report, suite: str, cases: list[Case], executable: Path, jobs: int
) -> None:
    runnable = []
    disagreements = archives.disagreements(suite)
    for case in cases:
        if reason := skip_reason(case, disagreements):
            report.outcome(case, "skipped", reason)
        else:
            runnable.append(case)
    if not runnable:
        return
    if suite == LEGACY:
        vendored = [case for case in runnable if case.fork == DAO]
        if vendored:
            replay_parallel(report, VENDORED_LEGACY, vendored, executable, jobs)
        runnable = [case for case in runnable if case.fork != DAO]
        if not runnable:
            return
        paths = dict.fromkeys(f"{catalogue.LEGACY_ROOT}/{case.path}" for case in runnable)
        root = archives.unpack(catalogue.LEGACY, *paths) / catalogue.LEGACY_ROOT
    else:
        root = harness.unpack_read(SOURCES[suite], runnable)
    replay_parallel(report, root, runnable, executable, jobs)


def replay_parallel(
    report: Report, root: Path, cases: list[Case], executable: Path, jobs: int
) -> None:
    """Replay the fixture batches and merge each result into the report."""
    batches = partition_cases(cases, jobs)
    if len(batches) == 1:
        report.merge(replay_batch(root, batches[0], executable))
        return
    with ProcessPoolExecutor(max_workers=len(batches), mp_context=get_context("spawn")) as pool:
        futures = [pool.submit(replay_batch, root, batch, executable) for batch in batches]
        for future in futures:
            report.merge(future.result())


def table_cell(value: str) -> str:
    """Keep a fixture value on one line and escape Markdown table delimiters."""
    return " ".join(value.splitlines()).replace("|", "\\|")


def outcome_order(row: Outcome) -> tuple[str, int, str, str, str, str]:
    """Sort outcomes by suite, network order, format, status and reason."""
    suite, network, group, status, reason = row
    ranks = LEGACY_NETWORK_RANK if suite == LEGACY else EXECUTION_NETWORK_RANK
    return suite, ranks.get(network, len(ranks)), network, group, status, reason


def render_fork(fork: str, inventory: InventoryReply, counts: Counts) -> list[str]:
    """List the observed and missed rules for one active fork."""
    gas_rules = inventory.rules
    observed_gas = gas_rules & counts.gas_rules.keys()
    missed_gas = gas_rules - counts.gas_rules.keys()
    if unexpected := counts.gas_rules.keys() - gas_rules:
        raise RuntimeError(f"gas rules missing from the {fork} inventory: {sorted(unexpected)}")
    transactions = (
        "state-test transaction" if counts.state_transactions == 1 else "state-test transactions"
    )
    blocks = "block" if counts.blocks == 1 else "blocks"
    return [
        "",
        f"## {fork}",
        "",
        f"Observed **{len(observed_gas)} of {len(gas_rules)}** instrumented gas rules.",
        f"Replay validated {counts.state_transactions} {transactions} and "
        f"{counts.blocks} {blocks} at this fork.",
        "",
        f"### Observed gas rules ({len(observed_gas)})",
        "",
        "| Gas rule | Events |",
        "| --- | ---: |",
        *(f"| `{rule}` | {counts.gas_rules[rule]} |" for rule in sorted(observed_gas)),
        "",
        f"### Missed gas rules ({len(missed_gas)})",
        "",
        *(f"- `{rule}`" for rule in sorted(missed_gas)),
        *([] if missed_gas else ["None."]),
    ]


def render_report(
    report: Report,
    sources: Mapping[str, str],
    request: Request,
    group: PurePosixPath | None = None,
    heze_supplement: bool = False,
) -> str:
    """Render the pinned sources, fixture outcomes, fork coverage and failures."""
    pinned = archives.fetch_archives.load(archives.REPO)
    sampled = {
        fork for fork, counts in report.counts.items() if counts.blocks or counts.state_transactions
    }
    unsampled = sorted({"bpo1", "bpo2", "bpo3", "bpo4", "bpo5"} - sampled)
    legacy_networks = {row[1] for row in report.outcomes if row[0] == LEGACY}
    legacy_scope = []
    if DAO in legacy_networks:
        legacy_scope.append(f"vendored `{DAO}` block fixtures")
    if legacy_networks - {DAO}:
        legacy_scope.append("selected archived gas fixtures in block form")
    fixture_scope = {LEGACY: " and ".join(legacy_scope)}
    if heze_supplement:
        networks = {row[1] for row in report.outcomes if row[0] == HEZE}
        labels = ", ".join(f"`{network}`" for network in sorted(networks))
        fixture_scope[HEZE] = f"Block fixtures for {labels}"
    lines = [
        "# Gas-rule coverage of execution fixtures",
        "",
        "Counts come from fixtures that passed their parity checks.",
        "Each accepted block contributes to the fork active at its number and timestamp.",
        "Block events come from transactions and system contract calls.",
        "An event is one occurrence of a named rule during replay.",
        "",
        "The inventory covers instrumented transaction, settlement and opcode pricing rules.",
        "It records completed step charges, even when a later step reverts the frame.",
        "The observer counts the implicit `STOP` at the end of nonempty code.",
        "The inventory omits partial charges on exceptional halts, gas returned by child frames, "
        "precompile pricing and code-deposit gas.",
        "From Pectra, refund events come from receipts whose gas used exceeds the calldata floor.",
        "The `at-floor` label includes cases where the gas after the refund equals the floor.",
        "",
        "Missed entries refer to the selected fixtures and the rules listed by the observer.",
        "The observer supports execution through Amsterdam.",
        "The fixture indexes call Hegotá `Bogota`.",
        *(["", f"Archive directory filter `{group}`."] if group is not None else []),
        *(
            [
                "",
                "Blob-schedule forks with no validated execution in this selection are "
                + ", ".join(f"`{fork}`" for fork in unsampled)
                + ".",
            ]
            if unsampled and group is None and "execution-spec-tests" in sources
            else []
        ),
        "",
        "## Pinned fixture sources",
        "",
        "| Suite | Archive | Archive SHA-256 | Fixtures |",
        "| --- | --- | --- | --- |",
        *(
            f"| {suite} | [{name}]({pinned[name].url}) | `{pinned[name].sha256}` | "
            f"{fixture_scope.get(suite, 'Release index')} |"
            for suite, name in sources.items()
        ),
        "",
        "## Fixture outcomes",
        "",
        "| Suite | Network | Format | Outcome | Reason | Cases |",
        "| --- | --- | --- | --- | --- | ---: |",
        *(
            "| " + " | ".join(map(table_cell, row)) + f" | {count} |"
            for row, count in sorted(
                report.outcomes.items(), key=lambda item: outcome_order(item[0])
            )
        ),
    ]
    inventories = []
    for fork, counts in report.counts.items():
        inventory = parse_inventory_reply(request({"kind": "inventory", "fork": fork}), fork)
        inventories.append((inventory.fork_index, fork, inventory, counts))
    for _, fork, inventory, counts in sorted(inventories):
        lines.extend(render_fork(fork, inventory, counts))
    if report.failures:
        lines.extend(
            (
                "",
                "## Failed fixture checks",
                "",
                "| Suite | Fixture | Network | Format | Error |",
                "| --- | --- | --- | --- | --- |",
            )
        )
        lines.extend(
            f"| {case.suite} | `{table_cell(case.id)}` | {case.fork} | {case.group} | "
            f"{table_cell(error)} |"
            for case, error in sorted(
                report.failures,
                key=lambda item: (item[0].suite, item[0].path, item[0].id, item[0].fork),
            )
        )
    return "\n".join(lines)


def main() -> None:
    """Run the selected fixtures and exit with status 1 when a fixture fails."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        action="append",
        choices=SOURCES,
        help="select a pinned suite (default: the execution release plus legacy and BPO fixtures)",
    )
    parser.add_argument("--network", action="append", help="select a fixture network")
    parser.add_argument("--format", action="append", help="select a fixture format from the index")
    parser.add_argument("--group", type=PurePosixPath, help="select a directory in the archive")
    parser.add_argument("--executable", type=Path, default=EXECUTABLE, help="path to gas-coverage")
    parser.add_argument(
        "--jobs", type=int, default=1, help=f"replay workers from 1 to {MAX_JOBS} (default: 1)"
    )
    args = parser.parse_args()
    if not __debug__:
        parser.error("fixture validation requires Python assertions")
    if not args.executable.is_file():
        parser.error("build the coverage executable with lake build gas-coverage")
    if not os.access(args.executable, os.X_OK):
        parser.error(f"coverage executable lacks execute permission: {args.executable}")
    if not 1 <= args.jobs <= MAX_JOBS:
        parser.error(f"--jobs must be from 1 to {MAX_JOBS}")

    networks, formats = set(args.network or ()), set(args.format or ())
    heze_supplement = not args.suite
    suites = args.suite or DEFAULT_SUITES
    sources = {
        suite: SOURCES[suite]
        for suite in suites
        if source_matches(suite, networks, formats, args.group)
        and (
            suite != HEZE
            or not heze_supplement
            or heze_supplement_matches(networks, formats, args.group)
        )
    }
    if archives.CACHE is None and any(suite != LEGACY for suite in sources):
        parser.error("set ETHLIB_ARCHIVES to the fixture archive cache directory")
    executable = args.executable.resolve()
    report = Report()
    for suite, archive in sources.items():
        cases = select_cases(
            source_cases(suite, archive, heze_supplement), networks, formats, args.group
        )
        if archives.CACHE is None and any(case.path in LEGACY_GAS_CASES for case in cases):
            parser.error("set ETHLIB_ARCHIVES to the fixture archive cache directory")
        replay_source(report, suite, cases, executable, args.jobs)
    if not report.outcomes:
        parser.error("no fixtures match the selection")
    with open_bridge(executable) as bridge:
        selected_suites = {row[0] for row in report.outcomes}
        selected_sources = {
            suite: name for suite, name in sources.items() if suite in selected_suites
        }
        output = render_report(
            report, selected_sources, bridge.request, args.group, heze_supplement
        )
    print(output)
    if report.failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
