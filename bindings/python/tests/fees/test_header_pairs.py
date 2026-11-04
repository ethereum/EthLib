"""The base fee and the excess blob gas against the headers of the blockchain tests."""

import json
from pathlib import Path

import pytest

from ethlib.execution.fees import calc_excess_blob_gas, calculate_base_fee_per_gas

_FILE = Path(__file__).resolve().parents[4] / "tests" / "execution" / "fees" / "header_pairs.json"
PAIRS = json.loads(_FILE.read_text())

# The network of a fixture, and the case of the Lean fork type that it names.
FORK_OF_NETWORK = {
    "Frontier": "frontier",
    "Homestead": "homestead",
    "TangerineWhistle": "tangerineWhistle",
    "SpuriousDragon": "spuriousDragon",
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
    "BPO1": "bpo1",
    "BPO2": "bpo2",
}

# A transition network runs its second fork from this timestamp on.
TRANSITION_TIME = 15_000


def fork_of(network: str, timestamp: int) -> str:
    """The fork of a block of a network, such as `OsakaToBPO1AtTime15k`."""
    if "To" not in network:
        return FORK_OF_NETWORK[network]
    before, after = network.removesuffix("AtTime15k").split("To")
    return FORK_OF_NETWORK[after if timestamp >= TRANSITION_TIME else before]


def _id(pair: dict) -> str:
    return f"{pair['network']}-{Path(pair['file']).stem}-{pair['test'][-60:]}-{pair['block']}"


def _excess(pair: dict) -> int:
    """The excess blob gas that EthLib computes for the child of a pair."""
    parent, child = pair["parent"], pair["child"]
    # EIP-4844: a parent from before the fork counts as 0 excess blob gas and 0 blob gas used.
    return calc_excess_blob_gas(
        fork_of(pair["network"], child["timestamp"]),
        parent.get("excessBlobGas", 0),
        parent.get("blobGasUsed", 0),
        parent["baseFeePerGas"],
    )


VALID = [pytest.param(p, id=_id(p)) for p in PAIRS if p["valid"]]
WRONG_EXCESS = [pytest.param(p, id=_id(p)) for p in PAIRS if not p["valid"]]


def test_counts():
    """The file holds 2,971 valid pairs and 1,178 children with a wrong excess blob gas."""
    assert (len(VALID), len(WRONG_EXCESS)) == (2971, 1178)


@pytest.mark.parametrize("pair", VALID)
def test_valid_child(pair: dict) -> None:
    """A valid child carries the base fee and the excess blob gas that its parent gives."""
    parent, child = pair["parent"], pair["child"]
    if "baseFeePerGas" in child:
        # No fixture crosses London, so a child with a base fee has a parent with one.
        expected = calculate_base_fee_per_gas(
            parent["gasLimit"], parent["gasUsed"], parent["baseFeePerGas"]
        )
        assert expected == child["baseFeePerGas"]
    if "excessBlobGas" in child:
        assert _excess(pair) == child["excessBlobGas"]


@pytest.mark.parametrize("pair", WRONG_EXCESS)
def test_wrong_excess_blob_gas(pair: dict) -> None:
    """A child that the fixture rejects for its excess blob gas carries another value."""
    assert _excess(pair) != pair["child"]["excessBlobGas"]
