"""Check the fields of every listed disagreement, from the file alone, without an archive."""

import pytest

import archives
from raising import raises

from . import harness

ENTRIES = archives.disagreement_entries()

# A legacy entry that gives every field right.
# Its command is written out in full, so that a change to the format of the command shows here.
ENTRY = {
    "suite": "legacytests",
    "case": "Constantinople/BlockchainTests/bcExample/example.json::example_Frontier",
    "group": "legacy_header",
    "reason": "a reason",
    "source": "a source",
    "class": "fixture-defect",
    "reproduce": 'pytest -m archive "bindings/python/tests/parity/test_legacy.py::test_case'
    '[legacy_header:Constantinople/BlockchainTests/bcExample/example.json::example_Frontier]"',
    "upstream": "As of 2026-11-11, there is no report upstream",
}

# Each change makes one field of the entry wrong, and None removes the field.
WRONG = {
    "command that names no case": {"reproduce": "pytest nonsense"},
    "command of another case": {
        "reproduce": ENTRY["reproduce"].replace("example_Frontier]", "example_Homestead]")
    },
    "command without the mark": {"reproduce": ENTRY["reproduce"].replace("-m archive ", "")},
    "legacy case without its group": {"group": None},
    "no reason": {"reason": None},
    "no source": {"source": None},
    "unknown class": {"class": "unknown"},
    "no state upstream": {"upstream": None},
    "state upstream without its date": {"upstream": "There is no report upstream"},
}


# Each entry takes the identifier of its case in the parity test of its suite.
@pytest.mark.parametrize(
    "entry",
    ENTRIES,
    ids=lambda entry: harness.case_id(entry["suite"], entry["case"], entry.get("group")),
)
def test_entry(entry) -> None:
    harness.check_entry(entry)


def test_right_entry() -> None:
    harness.check_entry(ENTRY)


@pytest.mark.parametrize("change", WRONG.values(), ids=WRONG.keys())
def test_wrong_entry(change) -> None:
    entry = {**ENTRY, **change}
    entry = {field: value for field, value in entry.items() if value is not None}
    # The check names the entry by its suite, case and group.
    key = (entry["suite"], entry["case"], entry.get("group"))
    with raises(AssertionError, str(key)):
        harness.check_entry(entry)
