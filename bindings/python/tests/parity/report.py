"""The parity report: passed, disagreed, failed and not yet runnable cases, per row."""

import json
import os
from collections import Counter, defaultdict
from pathlib import Path

# The environment variable that names the Markdown file of the report.
ENVIRONMENT = "ETHLIB_PARITY_REPORT"

# The outcome of each run case, and the catalogue of each suite, as the tests record them.
_outcomes: dict[str, Counter] = defaultdict(Counter)
_catalogue: dict[str, dict] = {}


def record(report) -> None:
    """Count the outcome of one test report of a parity test."""
    properties = dict(report.user_properties)
    if "parity catalogue" in properties and report.when == "call":
        _catalogue.update(json.loads(properties["parity catalogue"]))
    row = properties.get("parity row")
    if row is None:
        return
    if report.when == "call" and report.passed:
        _outcomes[row]["passed"] += 1
    elif report.when == "call" and report.skipped and hasattr(report, "wasxfail"):
        _outcomes[row]["disagreed"] += 1
    elif report.failed:
        _outcomes[row]["failed"] += 1


def _percent(part: int, whole: int) -> str:
    return f"{100 * part / whole:.1f} %" if whole else "-"


def markdown() -> str:
    """The report as Markdown: one table per suite, one row per preset, fork and runner."""
    lines = ["# Parity with the official test suites", ""]
    lines.append("A case passes, disagrees for a listed reason, fails, or waits for a runner.")
    lines.append("")
    by_suite = defaultdict(list)
    order = sorted(_catalogue, key=lambda row: (row.split(" ")[:2], _catalogue[row]["rank"], row))
    for row in order:
        by_suite[row.split(" ")[0]].append(row)
    for suite, rows in by_suite.items():
        lines += [
            f"## {suite}",
            "",
            "| Preset | Fork | Runner | Cases | Passed | Disagreed | Failed | "
            "Not yet runnable | Passed of all | Waits for |",
            "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |",
        ]
        for row in rows:
            _, preset, fork, runner = row.split(" ")
            entry, done = _catalogue[row], _outcomes[row]
            waiting = entry["cases"] - entry["runnable"]
            lines.append(
                f"| {preset} | {fork} | {runner} | {entry['cases']} | {done['passed']} | "
                f"{done['disagreed']} | {done['failed']} | {waiting} | "
                f"{_percent(done['passed'], entry['cases'])} | {entry['plan'] or ''} |"
            )
        total = Counter()
        for row in rows:
            total.update({"cases": _catalogue[row]["cases"], **_outcomes[row]})
        lines += [
            "",
            f"In all, {total['passed']} of {total['cases']} cases pass "
            f"({_percent(total['passed'], total['cases'])}).",
            f"{total['disagreed']} disagree for a listed reason, and {total['failed']} fail.",
            "",
        ]
    return "\n".join(lines)


def write() -> None:
    """Write the report to the file that `ETHLIB_PARITY_REPORT` names, and to the job summary."""
    if not _catalogue:
        return
    text = markdown()
    for variable in (ENVIRONMENT, "GITHUB_STEP_SUMMARY"):
        if path := os.environ.get(variable):
            with Path(path).open("a", encoding="utf-8") as out:
                out.write(text + "\n")
