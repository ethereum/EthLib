"""MODEXP at every fork from Byzantium, against the EIP-198 state tests of execution-specs."""

# `tests/execution/modexp/README.md` gives the origin of the calls and how they were read.

import json
from pathlib import Path

import pytest

from ethlib.errors import PrecompileError
from ethlib.precompiles import price, run

from .forks import since

_FILE = Path(__file__).resolve().parents[4] / "tests" / "execution" / "modexp" / "eip198_calls.json"
CALLS = json.loads(_FILE.read_text())

# The network of a fixture, and the case of the Lean fork type that it names.
FORK_OF_NETWORK = {
    "Byzantium": "byzantium",
    "ConstantinopleFix": "petersburg",
    "Istanbul": "istanbul",
    "Berlin": "berlin",
    "London": "london",
    "Paris": "paris",
    "Shanghai": "shapella",
    "Cancun": "dencun",
    "Prague": "pectra",
    "Osaka": "fusaka",
}


def test_counts():
    """47 calls at each of the 10 networks, 320 of them successful."""
    assert len(CALLS) == 470
    assert {call["network"] for call in CALLS} == set(FORK_OF_NETWORK)
    assert sum(call["success"] for call in CALLS) == 320


@pytest.mark.parametrize("call", CALLS, ids=[f"{c['network']}-{c['test'][-70:]}" for c in CALLS])
def test_call(call: dict) -> None:
    fork = FORK_OF_NETWORK[call["network"]]
    data = bytes.fromhex(call["input"].removeprefix("0x"))
    if call["success"]:
        # The call gets at most the gas limit of its transaction, so its price fits in it.
        gas = price(fork, 0x05, data)
        assert gas <= call["gasLimit"]
        assert "0x" + run(fork, 0x05, data, gas).hex() == call["output"]
    else:
        # Even with the whole gas limit of its transaction, the call fails.
        with pytest.raises(PrecompileError):
            run(fork, 0x05, data, call["gasLimit"])


# The forks that no network of the fixtures names share the rules of the fork before them.
BETWEEN = {
    "constantinople": "byzantium",
    "muirGlacier": "istanbul",
    "arrowGlacier": "london",
    "grayGlacier": "london",
    "bpo1": "fusaka",
    "bpo2": "fusaka",
    "bpo3": "fusaka",
    "bpo4": "fusaka",
    "bpo5": "fusaka",
}


def test_forks_between():
    """Every fork from Byzantium is a network of the fixtures or follows one."""
    assert set(since("byzantium")) == set(FORK_OF_NETWORK.values()) | set(BETWEEN)


@pytest.mark.parametrize("fork, same_as", sorted(BETWEEN.items()))
def test_call_between(fork: str, same_as: str) -> None:
    # Each call prices and runs at these forks as at the fork whose rules they keep.
    network = next(n for n, f in FORK_OF_NETWORK.items() if f == same_as)
    for call in CALLS:
        if call["network"] != network:
            continue
        data = bytes.fromhex(call["input"].removeprefix("0x"))
        assert price(fork, 0x05, data) == price(same_as, 0x05, data)
        if call["success"]:
            assert "0x" + run(fork, 0x05, data, call["gasLimit"]).hex() == call["output"]
        else:
            with pytest.raises(PrecompileError):
                run(fork, 0x05, data, call["gasLimit"])
