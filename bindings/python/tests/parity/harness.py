"""What the parity tests share: the runnable cases, the disagreements and the catalogue."""

import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

import pytest

import archives

from .catalogue import Case
from .runners import RUNNERS, plan, runner

# The test of each wheel runs the suites on Python 3.10 too.
if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib

DISAGREEMENTS_FILE = archives.REPO / "tests" / "parity" / "disagreements.toml"


def disagreements(suite: str) -> dict[tuple[str, str | None], dict]:
    """The listed disagreements of a suite, by case and group.

    An entry without a group holds for every group of its case.
    """
    entries = tomllib.loads(DISAGREEMENTS_FILE.read_text()).get("disagreement", [])
    return {
        (entry["case"], entry.get("group")): entry for entry in entries if entry["suite"] == suite
    }


def runnable(cases: list[Case]) -> list[Case]:
    """The cases that a runner covers."""
    return [case for case in cases if runner(case) is not None]


def unpack(name: str, cases: list[Case], depth: int) -> Path:
    """The archive `name`, with the first `depth` directories of each runnable case unpacked."""
    paths = sorted({"/".join(case.path.split("/")[:depth]) for case in runnable(cases)})
    if not paths:
        return archives.CACHE
    return archives.unpack(name, *paths)


def run(root: Path, case: Case, suite_disagreements: dict, request, record_property) -> None:
    """Run one case, which must fail with the listed reason if it is a disagreement."""
    record_property("parity row", case.row)
    entry = suite_disagreements.get((case.id, case.group)) or suite_disagreements.get(
        (case.id, None)
    )
    if entry is not None:
        request.applymarker(pytest.mark.xfail(strict=True, reason=entry["reason"]))
    runner(case)(root, case)


def catalogue(cases: list[Case]) -> str:
    """The number of cases and of runnable cases of each row, and the plan for the others."""
    rows: defaultdict[str, dict[str, Any]] = defaultdict(
        lambda: {"cases": 0, "runnable": 0, "plans": set()}
    )
    for case in cases:
        entry = rows[case.row]
        entry["rank"] = case.rank
        entry["cases"] += 1
        if runner(case) is not None:
            entry["runnable"] += 1
        else:
            entry["plans"].add(plan(case) or "no plan")
    return json.dumps(
        {
            row: {
                "rank": entry["rank"],
                "cases": entry["cases"],
                "runnable": entry["runnable"],
                "plan": "; ".join(sorted(entry["plans"])),
            }
            for row, entry in rows.items()
        }
    )


def check_groups(cases: list[Case]) -> None:
    """Every group has a runner or a plan, so that a new upstream group cannot go unnoticed."""
    missing = sorted(
        {case.group for case in cases if case.group not in RUNNERS and plan(case) is None}
    )
    assert missing == []


def check_disagreements(cases: list[Case], suite_disagreements: dict) -> None:
    """Every disagreement names a runnable case, with a reason and a source."""
    keys = {key for case in runnable(cases) for key in ((case.id, case.group), (case.id, None))}
    for key, entry in suite_disagreements.items():
        assert key in keys, key
        assert entry.get("reason") and entry.get("source"), key
