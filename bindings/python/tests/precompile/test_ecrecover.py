"""The ECRECOVER precompile against the cases of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.precompiles import price, run

from .forks import FORKS, ends

ADDRESS = 0x01

# The price of every call, from Appendix E of the Yellow Paper, at every fork.
GAS = 3000

# Every case of `test_precompiles`: the 128-byte input `hash || v || r || s`, and the output.
# They were read from the file's `pytest.param` lists, without running anything.
#
# File: tests/frontier/precompiles/test_ecrecover.py
# Repository: ethereum/execution-specs
# Commit: e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e
# Licence: CC0-1.0
CASES = json.loads((Path(__file__).resolve().parent / "ecrecover_cases.json").read_text())


@pytest.mark.parametrize("fork", FORKS)
def test_price(fork: str) -> None:
    assert price(fork, ADDRESS, b"") == GAS
    assert price(fork, ADDRESS, bytes(1000)) == GAS


@pytest.mark.parametrize("case", CASES, ids=[c["id"] for c in CASES])
@pytest.mark.parametrize("fork", ends("frontier"))
def test_execution_specs(fork: str, case: dict) -> None:
    assert run(fork, ADDRESS, bytes.fromhex(case["input"]), GAS) == bytes.fromhex(case["output"])


@pytest.mark.parametrize("fork", ends("frontier"))
def test_out_of_gas(fork: str) -> None:
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, ADDRESS, bytes.fromhex(CASES[0]["input"]), GAS - 1)


def test_trailing_bytes_ignored() -> None:
    case = CASES[0]
    data = bytes.fromhex(case["input"])
    assert run("bpo2", ADDRESS, data + b"\x01" * 50, GAS) == bytes.fromhex(case["output"])
