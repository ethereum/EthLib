"""P256VERIFY against every vector of EIP-7951.

`eip7951_cases.json` holds every case of the test vectors of EIP-7951.

File: assets/eip-7951/test-vectors.json
Repository: ethereum/EIPs
Commit: 0ce679f4654ba4d120c97113626f320475e22fa9

The EIP derives them from a Wycheproof set.

File: ecdsa_secp256r1_sha256_p1363_test.json
Repository: C2SP/wycheproof
Licence: Apache 2.0 (scripts/Apache-2.0.txt)

Each case runs with the price, 6900 gas.
The EIP lists 3450 gas, the price of an earlier draft, so that field is dropped.
"""

import json
from pathlib import Path

import pytest

from ethlib.precompiles import run

from .forks import ends

# The fork that adds the precompile, fusaka, and the latest fork: no fork in between changes it.
FORKS = ends("fusaka")

CASES = json.loads((Path(__file__).parent / "eip7951_cases.json").read_text())


@pytest.mark.parametrize("case", CASES, ids=[case["Name"] for case in CASES])
@pytest.mark.parametrize("fork", FORKS)
def test_vector(fork: str, case: dict) -> None:
    # A valid signature gives the word 1, and every invalid input gives empty output.
    assert run(fork, 0x100, bytes.fromhex(case["Input"]), 6900).hex() == case["Expected"]


@pytest.mark.parametrize("fork", FORKS)
def test_out_of_gas(fork: str) -> None:
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, 0x100, bytes.fromhex(CASES[0]["Input"]), 6899)
