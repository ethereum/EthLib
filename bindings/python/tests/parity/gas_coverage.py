"""Report the gas rules exercised by pinned execution fixtures."""

import argparse
import json
import subprocess
from collections import Counter
from collections.abc import Callable, Generator, Iterable, Mapping, Set
from concurrent.futures import ProcessPoolExecutor
from contextlib import contextmanager
from dataclasses import dataclass, field
from multiprocessing import get_context
from pathlib import Path, PurePosixPath
from typing import IO

import pytest

import archives

from . import catalogue, legacy, runners
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
FORMATS = {
    "blockchain_test_engine": "the coverage runner does not replay Engine API calls",
    "blockchain_test_engine_x": "the coverage runner does not replay Engine API calls",
    "blockchain_test_engine_reorg": "the coverage runner does not replay reorgs",
    "blockchain_test_sync": "client synchronization has no execution fixture runner",
    "transaction_test": "transaction admission does not execute EVM code",
}
RUNNABLE = {"state_test", "blockchain_test"}
EXECUTABLE = archives.REPO / ".lake/build/bin/gas-coverage"
Request = Callable[[dict], dict]
Outcome = tuple[str, str, str, str, str]


class FixtureError(ValueError):
    """The interpreter rejected a transaction or block."""


@dataclass
class Bridge:
    """One request and response per line of the coverage subprocess."""

    stdin: IO[str]
    stdout: IO[str]

    def request(self, payload: dict) -> dict:
        self.stdin.write(json.dumps(payload, separators=(",", ":")) + "\n")
        self.stdin.flush()
        line = self.stdout.readline()
        if not line:
            raise RuntimeError("gas-coverage stopped before replying")
        result = json.loads(line)
        if "error" in result:
            raise FixtureError(result["error"]["message"])
        return result


@contextmanager
def open_bridge(executable: Path) -> Generator[Bridge, None, None]:
    with subprocess.Popen(
        [str(executable)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True
    ) as process:
        assert process.stdin is not None and process.stdout is not None
        yield Bridge(process.stdin, process.stdout)
        process.stdin.close()
        if process.wait():
            raise RuntimeError("gas-coverage exited with an error")


@dataclass
class Counts:
    gas_rules: Counter[str] = field(default_factory=Counter)
    state_transactions: int = 0
    blocks: int = 0

    def merge(self, other: "Counts") -> None:
        self.gas_rules.update(other.gas_rules)
        self.state_transactions += other.state_transactions
        self.blocks += other.blocks


@dataclass
class Report:
    outcomes: Counter[Outcome] = field(default_factory=Counter)
    counts: dict[str, Counts] = field(default_factory=dict)
    failures: list[tuple[Case, str]] = field(default_factory=list)

    def outcome(self, case: Case, status: str, reason: str = "") -> None:
        self.outcomes[case.suite, case.fork, case.group, status, reason] += 1

    def merge(self, other: "Report") -> None:
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
        (
            case
            for case in cases
            if (not networks or case.fork in networks)
            and (not formats or case.group in formats)
            and (group is None or group in PurePosixPath(case.path).parents)
        ),
        key=lambda case: (case.path, case.id, case.fork),
    )


def heze_supplement_matches(
    networks: Set[str], formats: Set[str], group: PurePosixPath | None
) -> bool:
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
    fixtures = PurePosixPath("fixtures")
    if suite == LEGACY:
        return (not formats or LEGACY_FORMAT in formats) and (
            group is None or not group.is_relative_to(fixtures)
        )
    if (formats and formats <= {LEGACY_FORMAT}) or (networks and networks <= {DAO, "EIP150"}):
        return False
    return group is None or group.is_relative_to(fixtures) or fixtures.is_relative_to(group)


def source_cases(suite: str, archive: str, heze_supplement: bool = False) -> Iterable[Case]:
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
    if (case.id, case.group) in disagreements or (case.id, None) in disagreements:
        return "listed parity disagreement"
    if case.suite == LEGACY:
        return ""
    if case.fork in catalogue.BOGOTA_NETWORKS:
        return "Bogota devnet rules are outside the implemented execution forks"
    if case.fork not in catalogue.EXECUTION_FORKS:
        return "fixture network is outside the implemented execution forks"
    if case.group == "state_test" and case.fork not in runners.FORK_OF_NETWORK:
        return "no transaction fork is defined for this fixture network"
    if case.group not in RUNNABLE:
        return FORMATS.get(case.group, "no coverage runner for this fixture format")
    return ""


def replay_state(root: Path, case: Case, request: Request) -> dict[str, Counts]:
    (fork, chain_id, tx, pre, env), post = runners.state_test_input(root, case)
    expected = post.get("expectException")
    try:
        response = request(
            {
                "kind": "state",
                "fork": fork,
                "chainId": chain_id,
                "tx": tx.hex(),
                "state": pre.hex(),
                "env": env.hex(),
            }
        )
    except FixtureError as error:
        if expected is None:
            raise
        assert any(runners.names_in_block(name, str(error)) for name in expected.split("|")), (
            expected,
            str(error),
        )
        return {}
    if expected is not None:
        raise AssertionError(f"transaction accepted despite expected exception {expected}")
    assert bytes.fromhex(response["stateRoot"]) == bytes.fromhex(post["hash"][2:]), (
        "state root differs"
    )
    runners.check_state_test_receipt(
        post, bytes.fromhex(response["logsHash"]), response["gasUsed"], response["succeeded"]
    )
    if pinned := post.get("receipt", {}).get("rlp"):
        assert bytes.fromhex(response["receipt"]) == bytes.fromhex(pinned[2:]), (
            "receipt bytes differ"
        )
    return {fork: Counts(Counter(response["gasRules"]), state_transactions=1)}


def replay_blockchain(root: Path, case: Case, request: Request) -> dict[str, Counts]:
    by_fork: dict[str, Counts] = {}

    def transition(
        config: dict, state: bytes, recent: legacy.RecentBlocks, fork: str, raw: bytes, seal: bool
    ) -> bytes:
        if isinstance(address := config.get("depositContractAddress"), bytes):
            config = {**config, "depositContractAddress": "0x" + address.hex()}
        response = request(
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
        raw_state = bytes.fromhex(response["state"])
        counts = by_fork.setdefault(fork, Counts())
        counts.gas_rules.update(response["gasRules"])
        counts.blocks += 1
        return raw_state

    if case.group == LEGACY_FORMAT:
        legacy.run_blockchain(root, case, transition=transition)
    else:
        runners.check_blockchain_test(root, case, transition)
    return by_fork


def replay_cases(root: Path, cases: list[Case], request: Request) -> Report:
    report = Report()
    for case in cases:
        replay = replay_state if case.group == "state_test" else replay_blockchain
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
        root = archives.unpack(SOURCES[suite], *dict.fromkeys(case.path for case in runnable))
    replay_parallel(report, root, runnable, executable, jobs)


def replay_parallel(
    report: Report, root: Path, cases: list[Case], executable: Path, jobs: int
) -> None:
    batches = partition_cases(cases, jobs)
    if len(batches) == 1:
        report.merge(replay_batch(root, batches[0], executable))
        return
    with ProcessPoolExecutor(max_workers=len(batches), mp_context=get_context("spawn")) as pool:
        futures = [pool.submit(replay_batch, root, batch, executable) for batch in batches]
        for future in futures:
            report.merge(future.result())


def table_cell(value: str) -> str:
    return " ".join(value.splitlines()).replace("|", "\\|")


def render_fork(fork: str, inventory: dict, counts: Counts) -> list[str]:
    gas_rules = set(inventory["gasRules"])
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
        fixture_scope[HEZE] = "Block fixtures for BPO2 → BPO3 and BPO3 → BPO4"
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
            for row, count in sorted(report.outcomes.items())
        ),
    ]
    for fork in sorted(report.counts):
        inventory = request({"kind": "inventory", "fork": fork})
        lines.extend(render_fork(fork, inventory, report.counts[fork]))
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
    parser.add_argument("--jobs", type=int, default=1, help="maximum replay workers (default: 1)")
    args = parser.parse_args()
    if not __debug__:
        parser.error("fixture validation requires Python assertions")
    if not args.executable.is_file():
        parser.error("build the coverage executable with lake build gas-coverage")
    if args.jobs < 1:
        parser.error("--jobs must be positive")

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
