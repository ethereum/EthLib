"""The place of each fixture format of execution-spec-tests, without the archives."""

import pytest

from . import runners
from .catalogue import EXCLUDED_FORMATS, in_scope
from .harness import unplaced_formats
from .runners import FORMAT_RUNNERS


def _index(*formats: str) -> list[dict]:
    """A release index with one entry of each format."""
    return [{"format": name} for name in formats]


def test_formats_that_run_or_are_left_out_are_placed():
    assert unplaced_formats(_index(*FORMAT_RUNNERS, *EXCLUDED_FORMATS)) == []


def test_a_planned_format_is_placed(monkeypatch: pytest.MonkeyPatch):
    monkeypatch.setitem(runners.NOT_YET, "planned_test", "the runner that brings it")
    assert unplaced_formats(_index("state_test", "planned_test")) == []


def test_new_formats_are_named_by_name():
    # Six names in reverse order, so that the order of a set rarely sorts them by chance.
    new = [f"{letter}_unknown_test" for letter in "fedcba"]
    assert unplaced_formats(_index("state_test", *new, "blockchain_test_sync")) == sorted(new)


def test_a_format_left_out_has_no_runner_and_no_plan():
    assert EXCLUDED_FORMATS.keys() & (FORMAT_RUNNERS.keys() | runners.NOT_YET.keys()) == set()


@pytest.mark.parametrize("name", list(EXCLUDED_FORMATS))
def test_a_format_left_out_gives_no_cases(name: str):
    assert not in_scope(name)


@pytest.mark.parametrize("name", [*FORMAT_RUNNERS, "unknown_test"])
def test_a_format_that_runs_or_is_new_gives_cases(name: str):
    # A format that is new upstream becomes cases, so the check of the groups sees it.
    assert in_scope(name)
