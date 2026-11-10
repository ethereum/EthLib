"""Consensus steps on amounts above 2^53, and on sums that pass the range of a uint64."""

import hashlib
from pathlib import Path

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from . import test_epoch_processing, test_operations
from .containers import FORKS

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "large_amounts"

# The rejection of a step whose balance, or a sum of amounts, leaves the range of a uint64.
OVERFLOW = (
    "EthLib.Consensus.TransitionError.accessor "
    "(EthLib.Consensus.AccessorError.arith (EthLib.Base.ArithError.overflow))"
)


def _cases(rejected: bool) -> list:
    """The vendored cases that have a post state, or else the rejected ones."""
    cases = []
    for pre in sorted((FILES / "minimal").rglob("pre.ssz_snappy")):
        case = pre.parent
        if (case / "post.ssz_snappy").exists() == rejected:
            continue
        preset, fork, runner, handler = case.relative_to(FILES).parts[:4]
        cases.append(
            pytest.param(preset, fork, runner, handler, case, id=case.relative_to(FILES).as_posix())
        )
    return cases


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text().splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(
        1
        for path in FILES.rglob("*")
        if path.is_file()
        and path.name not in ("SHA256SUMS", "README.md")
        and "__pycache__" not in path.parts
    )
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


@pytest.mark.parametrize("preset, fork, runner, handler, case", _cases(False) + _cases(True))
def test_case(preset, fork, runner, handler, case):
    if runner == "operations":
        assert test_operations.runs(fork, handler)
        test_operations.run_case(preset, fork, handler, case)
    else:
        assert test_epoch_processing.runs(fork, handler)
        test_epoch_processing.run_case(preset, fork, handler, case)


@pytest.mark.parametrize("preset, fork, runner, handler, case", _cases(True))
def test_rejection_is_the_overflow(preset, fork, runner, handler, case):
    pre = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    with raises(consensus.TransitionError, OVERFLOW) as error:
        if runner == "operations":
            # From Gloas a withdrawals case has no operation: the state holds the withdrawals.
            name = test_operations.HANDLERS[handler][0]
            path = case / f"{name}.ssz_snappy"
            operation = snappy.decompress(path.read_bytes()) if path.exists() else b""
            consensus.process_operation(preset, FORKS[fork], handler, pre, operation)
        else:
            consensus.process_epoch(preset, FORKS[fork], handler, pre, None)
    assert error.value.code == 1
