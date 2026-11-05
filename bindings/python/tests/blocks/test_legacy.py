"""The vendored legacy blockchain tests of ethereum/legacytests, through the parity runners."""

import hashlib
import os

import pytest

import archives
from parity import catalogue, harness, legacy

VENDORED = archives.REPO / "tests" / "execution" / "legacytests"
CASES = harness.runnable(catalogue.legacy_cases(VENDORED))
DISAGREEMENTS = harness.disagreements("legacytests")

# A sealed block builds the 16 MiB Ethash cache of epoch 0, which takes seconds, so it runs weekly.
SLOW = os.environ.get("ETHLIB_SLOW_VECTORS") == "1"
slow = pytest.mark.skipif(not SLOW, reason="the Ethash cache of epoch 0, run weekly")


def _param(case: catalogue.Case):
    marks = [slow] if legacy.sealed(legacy.fixture(VENDORED, case)) else []
    return pytest.param(case, marks=marks, id=case.id)


@pytest.mark.parametrize("case", [_param(case) for case in CASES])
def test_case(case, request, record_property) -> None:
    harness.run(VENDORED, case, DISAGREEMENTS, request, record_property)


def test_vendored_cases_cover_both_seal_engines_and_a_transition() -> None:
    tests = [legacy.fixture(VENDORED, case) for case in CASES]
    assert any(legacy.sealed(test) for test in tests)
    assert any(not legacy.sealed(test) for test in tests)
    assert any(len(catalogue.LEGACY_FORKS[case.fork]) == 2 for case in CASES)


def test_digests() -> None:
    lines = (VENDORED / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for _ in VENDORED.rglob("*.json"))
    for digest, name in entries:
        assert hashlib.sha256((VENDORED / name).read_bytes()).hexdigest() == digest, name
